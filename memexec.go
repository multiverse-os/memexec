package memexec

import (
	"bytes"
	"context"
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"unsafe"
)

const maxint int64 = int64(^uint(0) >> 1)

const (
	MFD_CREATE  = 319
	MFD_CLOEXEC = 0x0001
)

type Error struct {
	Name string
	Err  error
}

func (self *Error) Error() string {
	return "[memexec] " + strconv.Quote(self.Name) + ": " + self.Err.Error()
}
func (self *Error) Unwrap() error { return self.Err }

type memFD struct {
	*os.File
}

func (self *memFD) Write(bytes []byte) (int, error) { return syscall.Write(int(self.Fd()), bytes) }
func (self *memFD) Path() string                    { return fmt.Sprintf("/proc/self/fd/%d", self.Fd()) }
func (self *memFD) Info() (os.FileInfo, error)      { return os.Lstat(self.Path()) }

type Cmd struct {
	name            string
	memFD           *memFD
	Size            int64
	Args            []string
	Env             []string
	Dir             string
	Stdin           io.Reader
	Stdout          io.Writer
	Stderr          io.Writer
	ExtraFiles      []*os.File
	SysProcAttr     *syscall.SysProcAttr
	Process         *os.Process
	ProcessState    *os.ProcessState
	ctx             context.Context // nil means none
	lookPathErr     error           // LookPath error, if any.
	finished        bool            // when Wait was called
	childFiles      []*os.File
	closeAfterStart []io.Closer
	closeAfterWait  []io.Closer
	goroutine       []func() error
	errch           chan error // one send per goroutine
	waitDone        chan struct{}
}

// TODO: Decide if its worth putting in name "memexec" (does it see this in ps
// aux? Or let the user set the name?
func Command(bytes []byte, args ...string) *Cmd {
	name := "memexec"
	fd, _, _ := syscall.Syscall(MFD_CREATE, uintptr(unsafe.Pointer(&name)), uintptr(MFD_CLOEXEC), 0)

	cmd := &Cmd{
		name: name,
		Args: args,
		memFD: &memFD{
			os.NewFile(fd, name),
		},
	}

	bytesWritten, err := cmd.memFD.Write(bytes)
	if err != nil {
		fmt.Errorf("[error] failed to write executable bytes to memory fd:", err)
	}
	cmd.Size = int64(bytesWritten)

	return cmd
}

func MemFD(fd *os.File, args ...string) *Cmd {
	cmd := &Cmd{
		Args: args,
		memFD: &memFD{
			File: fd,
		},
	}
	return cmd
}

func CommandContext(ctx context.Context, bytes []byte, arg ...string) *Cmd {
	if ctx == nil {
		panic("[fatal] nil Context")
	}
	cmd := Command(bytes, arg...)
	cmd.ctx = ctx
	return cmd
}

func (self *Cmd) commandWithArguments() []string {
	return append([]string{self.name}, self.Args...)
}

func (self *Cmd) String() string { return strings.Join(self.commandWithArguments(), " ") }

func interfaceEqual(a, b interface{}) bool {
	defer func() {
		recover()
	}()
	return a == b
}

func (self *Cmd) envv() []string {
	if self.Env != nil {
		return self.Env
	}
	return os.Environ()
}

var skipStdinCopyError func(error) bool

func (self *Cmd) stdin() (f *os.File, err error) {
	if self.Stdin == nil {
		f, err = os.Open(os.DevNull)
		if err != nil {
			return
		}
		self.closeAfterStart = append(self.closeAfterStart, f)
		return
	}
	if f, ok := self.Stdin.(*os.File); ok {
		return f, nil
	}
	pr, pw, err := os.Pipe()
	if err != nil {
		return
	}

	self.closeAfterStart = append(self.closeAfterStart, pr)
	self.closeAfterWait = append(self.closeAfterWait, pw)
	self.goroutine = append(self.goroutine, func() error {
		_, err := io.Copy(pw, self.Stdin)
		// TODO: Really? Sometimes the std libraries really need work..
		if skip := skipStdinCopyError; skip != nil && skip(err) {
			err = nil
		} else if err1 := pw.Close(); err == nil {
			err = err1
		}
		return err
	})
	return pr, nil
}

func (self *Cmd) stdout() (f *os.File, err error) { return self.writerDescriptor(self.Stdout) }

func (self *Cmd) stderr() (f *os.File, err error) {
	if self.Stderr != nil && interfaceEqual(self.Stderr, self.Stdout) {
		return self.childFiles[1], nil
	}
	return self.writerDescriptor(self.Stderr)
}

func (self *Cmd) writerDescriptor(w io.Writer) (f *os.File, err error) {
	if w == nil {
		f, err = os.OpenFile(os.DevNull, os.O_WRONLY, 0)
		if err != nil {
			return
		}
		self.closeAfterStart = append(self.closeAfterStart, f)
		return
	}

	if f, ok := w.(*os.File); ok {
		return f, nil
	}

	pr, pw, err := os.Pipe()
	if err != nil {
		return
	}

	self.closeAfterStart = append(self.closeAfterStart, pw)
	self.closeAfterWait = append(self.closeAfterWait, pr)
	self.goroutine = append(self.goroutine, func() error {
		_, err := io.Copy(w, pr)
		pr.Close() // in case io.Copy stopped due to write error
		return err
	})
	return pw, nil
}

func (self *Cmd) closeDescriptors(closers []io.Closer) {
	for _, fd := range closers {
		fd.Close()
	}
}

func (self *Cmd) Run() error {
	if err := self.Start(); err != nil {
		return err
	}
	return self.Wait()
}

func (self *Cmd) Start() error {
	if self.Process != nil {
		return fmt.Errorf("[memexec] already started")
	}
	if self.ctx != nil {
		select {
		case <-self.ctx.Done():
			self.closeDescriptors(self.closeAfterStart)
			self.closeDescriptors(self.closeAfterWait)
			return self.ctx.Err()
		default:
		}
	}

	self.childFiles = make([]*os.File, 0, 3+len(self.ExtraFiles))
	type F func(*Cmd) (*os.File, error)
	for _, setupFd := range []F{(*Cmd).stdin, (*Cmd).stdout, (*Cmd).stderr} {
		fd, err := setupFd(self)
		if err != nil {
			self.closeDescriptors(self.closeAfterStart)
			self.closeDescriptors(self.closeAfterWait)
			return err
		}
		self.childFiles = append(self.childFiles, fd)
	}
	self.childFiles = append(self.childFiles, self.ExtraFiles...)
	fmt.Println("arguments:", self.Args)
	fmt.Println("arguments with command:", append([]string{self.name}, self.Args...))
	var err error
	self.Process, err = os.StartProcess(
		self.memFD.Path(),
		append([]string{self.name}, self.Args...),
		&os.ProcAttr{
			Dir:   self.Dir,
			Files: self.childFiles,
			Env:   addCriticalEnv(dedupEnv(self.envv())),
			Sys:   self.SysProcAttr,
		},
	)

	if err != nil {
		self.closeDescriptors(self.closeAfterStart)
		self.closeDescriptors(self.closeAfterWait)
		return err
	}
	self.closeDescriptors(self.closeAfterStart)

	// Don't allocate the channel unless there are goroutines to fire.
	if len(self.goroutine) > 0 {
		self.errch = make(chan error, len(self.goroutine))
		for _, fn := range self.goroutine {
			go func(fn func() error) {
				self.errch <- fn()
			}(fn)
		}
	}

	if self.ctx != nil {
		self.waitDone = make(chan struct{})
		go func() {
			select {
			case <-self.ctx.Done():
				self.Process.Kill()
			case <-self.waitDone:
			}
		}()
	}
	return nil
}

type ExitError struct {
	*os.ProcessState
	Stderr []byte
}

func (self *ExitError) Error() string { return self.ProcessState.String() }

func (self *Cmd) Wait() error {
	if self.Process == nil {
		return fmt.Errorf("[memexec] not started")
	} else if self.finished {
		return fmt.Errorf("[memexec] Wait was already called")
	}
	self.finished = true

	state, err := self.Process.Wait()
	if self.waitDone != nil {
		close(self.waitDone)
	}
	self.ProcessState = state

	var copyError error
	for range self.goroutine {
		if err := <-self.errch; err != nil && copyError == nil {
			copyError = err
		}
	}

	self.closeDescriptors(self.closeAfterWait)

	if err != nil {
		return err
	} else if !state.Success() {
		return &ExitError{ProcessState: state}
	}

	return copyError
}

func (self *Cmd) Output() ([]byte, error) {
	if self.Stdout != nil {
		return nil, fmt.Errorf("[memexec] Stdout already set")
	}
	var stdout bytes.Buffer
	self.Stdout = &stdout

	captureErr := self.Stderr == nil
	if captureErr {
		self.Stderr = &prefixSuffixSaver{N: 32 << 10}
	}

	err := self.Run()
	if err != nil && captureErr {
		if ee, ok := err.(*ExitError); ok {
			ee.Stderr = self.Stderr.(*prefixSuffixSaver).Bytes()
		}
	}
	return stdout.Bytes(), err
}

func (self *Cmd) CombinedOutput() ([]byte, error) {
	if self.Stdout != nil {
		return nil, fmt.Errorf("[memexec] Stdout already set")
	} else if self.Stderr != nil {
		return nil, fmt.Errorf("[memexec] Stderr already set")
	}
	var b bytes.Buffer
	self.Stdout = &b
	self.Stderr = &b
	err := self.Run()
	return b.Bytes(), err
}

func (self *Cmd) StdinPipe() (io.WriteCloser, error) {
	if self.Stdin != nil {
		return nil, fmt.Errorf("[memexec] Stdin already set")
	} else if self.Process != nil {
		return nil, fmt.Errorf("[memexec] StdinPipe after process started")
	}
	pr, pw, err := os.Pipe()
	if err != nil {
		return nil, err
	}
	self.Stdin = pr
	self.closeAfterStart = append(self.closeAfterStart, pr)
	wc := &closeOnce{File: pw}
	self.closeAfterWait = append(self.closeAfterWait, wc)
	return wc, nil
}

type closeOnce struct {
	*os.File
	once sync.Once
	err  error
}

func (self *closeOnce) Close() error {
	self.once.Do(self.close)
	return self.err
}

func (self *closeOnce) close() { self.err = self.File.Close() }

func (self *Cmd) StdoutPipe() (io.ReadCloser, error) {
	if self.Stdout != nil {
		return nil, fmt.Errorf("[memexec] Stdout already set")
	} else if self.Process != nil {
		return nil, fmt.Errorf("[memexec] StdoutPipe after process started")
	}
	pr, pw, err := os.Pipe()
	if err != nil {
		return nil, err
	} else {
		self.Stdout = pw
		self.closeAfterStart = append(self.closeAfterStart, pw)
		self.closeAfterWait = append(self.closeAfterWait, pr)
		return pr, nil
	}
}

func (self *Cmd) StderrPipe() (io.ReadCloser, error) {
	if self.Stderr != nil {
		return nil, fmt.Errorf("[memexec] Stderr already set")
	} else if self.Process != nil {
		return nil, fmt.Errorf("[memexec] StderrPipe after process started")
	}
	pr, pw, err := os.Pipe()
	if err != nil {
		return nil, err
	}
	self.Stderr = pw
	self.closeAfterStart = append(self.closeAfterStart, pw)
	self.closeAfterWait = append(self.closeAfterWait, pr)
	return pr, nil
}

type prefixSuffixSaver struct {
	N         int // max size of prefix or suffix
	prefix    []byte
	suffix    []byte // ring buffer once len(suffix) == N
	suffixOff int    // offset to write into suffix
	skipped   int64
}

func (self *prefixSuffixSaver) Write(p []byte) (n int, err error) {
	lenp := len(p)
	p = self.fill(&self.prefix, p)
	// Only keep the last self.N bytes of suffix data.
	if overage := len(p) - self.N; overage > 0 {
		p = p[overage:]
		self.skipped += int64(overage)
	}
	p = self.fill(&self.suffix, p)
	// self.suffix is full now if p is non-empty. Overwrite it in a circle.
	for len(p) > 0 { // 0, 1, or 2 iterations.
		n := copy(self.suffix[self.suffixOff:], p)
		p = p[n:]
		self.skipped += int64(n)
		self.suffixOff += n
		if self.suffixOff == self.N {
			self.suffixOff = 0
		}
	}
	return lenp, nil
}

// fill appends up to len(p) bytes of p to *dst, such that *dst does not
// grow larger than self.N. It returns the un-appended suffix of p.
func (self *prefixSuffixSaver) fill(dst *[]byte, p []byte) (pRemain []byte) {
	if remain := self.N - len(*dst); remain > 0 {
		add := minInt(len(p), remain)
		*dst = append(*dst, p[:add]...)
		p = p[add:]
	}
	return p
}

func (self *prefixSuffixSaver) Bytes() []byte {
	if self.suffix == nil {
		return self.prefix
	} else if self.skipped == 0 {
		return append(self.prefix, self.suffix...)
	}
	var buf bytes.Buffer
	buf.Grow(len(self.prefix) + len(self.suffix) + 50)
	buf.Write(self.prefix)
	buf.WriteString("\n... omitting ")
	buf.WriteString(strconv.FormatInt(self.skipped, 10))
	buf.WriteString(" bytes ...\n")
	buf.Write(self.suffix[self.suffixOff:])
	buf.Write(self.suffix[:self.suffixOff])
	return buf.Bytes()
}

func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func dedupEnv(env []string) []string {
	return dedupEnvCase(env)
}

func dedupEnvCase(env []string) []string {
	out := make([]string, 0, len(env))
	saw := make(map[string]int, len(env)) // key => index into out
	for _, kv := range env {
		eq := strings.Index(kv, "=")
		if eq < 0 {
			out = append(out, kv)
			continue
		}
		k := kv[:eq]
		k = strings.ToLower(k)
		if dupIdx, isDup := saw[k]; isDup {
			out[dupIdx] = kv
			continue
		}
		saw[k] = len(out)
		out = append(out, kv)
	}
	return out
}

func addCriticalEnv(env []string) []string {
	for _, kv := range env {
		eq := strings.Index(kv, "=")
		if eq < 0 {
			continue
		}
		k := kv[:eq]
		if strings.EqualFold(k, "SYSTEMROOT") {
			return env
		}
	}
	return append(env, "SYSTEMROOT="+os.Getenv("SYSTEMROOT"))
}

func init() {
	skipStdinCopyError = func(err error) bool {
		// Ignore EPIPE errors copying to stdin if the program
		// completed successfully otherwise.
		// See Issue 9173.
		pe, ok := err.(*os.PathError)
		return ok &&
			pe.Op == "write" && pe.Path == "|1" &&
			pe.Err == syscall.EPIPE
	}
}
