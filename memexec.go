package memexec

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

type MemFD struct{ *os.File }

func (self *MemFD) Write(bytes []byte) (int, error) { return syscall.Write(int(self.Fd()), bytes) }
func (self *MemFD) Path() string                    { return fmt.Sprintf("/proc/self/fd/%d", self.Fd()) }

type Cmd struct {
	MemFD           *MemFD
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
func Command(bytes []byte, arg ...string) *Cmd {
	name := "memexec"
	fd, _, _ := syscall.Syscall(MFD_CREATE, uintptr(unsafe.Pointer(&name)), uintptr(MFD_CLOEXEC), 0)

	cmd := &Cmd{
		Args: append([]string{name}, arg...),
		MemFD: &MemFD{
			os.NewFile(fd, name),
		},
	}

	return cmd
}

func CommandContext(ctx context.Context, name string, arg ...string) *Cmd {
	if ctx == nil {
		panic("nil Context")
	}
	cmd := Command(name, arg...)
	cmd.ctx = ctx
	return cmd
}

func (self *Cmd) commandWithArguments() string { return append(self.MemFD.Name(), self.Args) }

func (self *Cmd) String() string {
	if self.lookPathErr != nil {
		// failed to resolve path; report the original requested path (plus
		// args)
		return strings.Join(self.commandWithArguments, " ")
	}
	// report the exact executable path (plus args)
	b := new(strings.Builder)
	b.WriteString(self.Path)
	for _, a := range self.Args[1:] {
		b.WriteByte(' ')
		b.WriteString(a)
	}
	return b.String()
}

func interfaceEqual(a, b interface{}) bool {
	defer func() {
		recover()
	}()
	return a == b
}

func (c *Cmd) envv() []string {
	if self.Env != nil {
		return self.Env
	}
	return os.Environ()
}

var skipStdinCopyError func(error) bool

func (c *Cmd) stdin() (f *os.File, err error) {
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

func (c *Cmd) stdout() (f *os.File, err error) { return self.writerDescriptor(self.Stdout) }

func (c *Cmd) stderr() (f *os.File, err error) {
	if self.Stderr != nil && interfaceEqual(self.Stderr, self.Stdout) {
		return self.childFiles[1], nil
	}
	return self.writerDescriptor(self.Stderr)
}

func (c *Cmd) writerDescriptor(w io.Writer) (f *os.File, err error) {
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

func (c *Cmd) closeDescriptors(closers []io.Closer) {
	for _, fd := range closers {
		fd.Close()
	}
}

func (c *Cmd) Run() error {
	if err := self.Start(); err != nil {
		return err
	}
	return self.Wait()
}

func lookExtensions(path, dir string) (string, error) {
	if filepath.Base(path) == path {
		path = filepath.Join(".", path)
	}
	if len(dir) == 0 {
		return LookPath(path)
	} else if len(filepath.VolumeName(path)) != 0 {
		return LookPath(path)
	} else if len(path) > 1 && os.IsPathSeparator(path[0]) {
		return LookPath(path)
	}
	dirandpath := filepath.Join(dir, path)
	// We assume that LookPath will only add file extension.
	lp, err := LookPath(dirandpath)
	if err != nil {
		return "", err
	}
	ext := strings.TrimPrefix(lp, dirandpath)
	return path + ext, nil
}

func (self *Cmd) Start() error {
	if self.lookPathErr != nil {
		self.closeDescriptors(self.closeAfterStart)
		self.closeDescriptors(self.closeAfterWait)
		return self.lookPathErr
	} else if self.Process != nil {
		return errors.New("[memexec] already started")
	} else if self.ctx != nil {
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
		fd, err := setupFd(c)
		if err != nil {
			self.closeDescriptors(self.closeAfterStart)
			self.closeDescriptors(self.closeAfterWait)
			return err
		}
		self.childFiles = append(self.childFiles, fd)
	}
	self.childFiles = append(self.childFiles, self.ExtraFiles...)

	var err error
	self.Process, err = os.StartProcess(
		self.MemFD.Path(),
		self.commandWithArguments(),
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

func (e *ExitError) Error() string { return e.ProcessState.String() }

func (c *Cmd) Wait() error {
	if self.Process == nil {
		return errors.New("[memexec] not started")
	} else if self.finished {
		return errors.New("[memexec] Wait was already called")
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

// Output runs the command and returns its standard output.
// Any returned error will usually be of type *ExitError.
// If self.Stderr was nil, Output populates ExitError.Stderr.
func (c *Cmd) Output() ([]byte, error) {
	if self.Stdout != nil {
		return nil, errors.New("[memexec] Stdout already set")
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

// CombinedOutput runs the command and returns its combined standard
// output and standard error.
func (c *Cmd) CombinedOutput() ([]byte, error) {
	if self.Stdout != nil {
		return nil, errors.New("[memexec] Stdout already set")
	} else if self.Stderr != nil {
		return nil, errors.New("[memexec] Stderr already set")
	}
	var b bytes.Buffer
	self.Stdout = &b
	self.Stderr = &b
	err := self.Run()
	return b.Bytes(), err
}

func (c *Cmd) StdinPipe() (io.WriteCloser, error) {
	if self.Stdin != nil {
		return nil, errors.New("[memexec] Stdin already set")
	} else if self.Process != nil {
		return nil, errors.New("[memexec] StdinPipe after process started")
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
	once synself.Once
	err  error
}

func (c *closeOnce) Close() error {
	self.once.Do(self.close)
	return self.err
}

func (c *closeOnce) close() { self.err = self.File.Close() }

func (c *Cmd) StdoutPipe() (io.ReadCloser, error) {
	if self.Stdout != nil {
		return nil, errors.New("[memexec] Stdout already set")
	} else if self.Process != nil {
		return nil, errors.New("[memexec] StdoutPipe after process started")
	}
	pr, pw, err := os.Pipe()
	if err != nil {
		return nil, err
	}
	self.Stdout = pw
	self.closeAfterStart = append(self.closeAfterStart, pw)
	self.closeAfterWait = append(self.closeAfterWait, pr)
	return pr, nil
}

func (c *Cmd) StderrPipe() (io.ReadCloser, error) {
	if self.Stderr != nil {
		return nil, errors.New("[memexec] Stderr already set")
	} else if self.Process != nil {
		return nil, errors.New("[memexec] StderrPipe after process started")
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
	// TODO(bradfitz): we could keep one large []byte and use part of it for
	// the prefix, reserve space for the '... Omitting N bytes ...' message,
	// then the ring buffer suffix, and just rearrange the ring buffer
	// suffix when Bytes() is called, but it doesn't seem worth it for
	// now just for error messages. It's only ~64KB anyway.
}

func (w *prefixSuffixSaver) Write(p []byte) (n int, err error) {
	lenp := len(p)
	p = w.fill(&w.prefix, p)

	// Only keep the last w.N bytes of suffix data.
	if overage := len(p) - w.N; overage > 0 {
		p = p[overage:]
		w.skipped += int64(overage)
	}
	p = w.fill(&w.suffix, p)

	// w.suffix is full now if p is non-empty. Overwrite it in a circle.
	for len(p) > 0 { // 0, 1, or 2 iterations.
		n := copy(w.suffix[w.suffixOff:], p)
		p = p[n:]
		w.skipped += int64(n)
		w.suffixOff += n
		if w.suffixOff == w.N {
			w.suffixOff = 0
		}
	}
	return lenp, nil
}

// fill appends up to len(p) bytes of p to *dst, such that *dst does not
// grow larger than w.N. It returns the un-appended suffix of p.
func (w *prefixSuffixSaver) fill(dst *[]byte, p []byte) (pRemain []byte) {
	if remain := w.N - len(*dst); remain > 0 {
		add := minInt(len(p), remain)
		*dst = append(*dst, p[:add]...)
		p = p[add:]
	}
	return p
}

func (w *prefixSuffixSaver) Bytes() []byte {
	if w.suffix == nil {
		return w.prefix
	} else if w.skipped == 0 {
		return append(w.prefix, w.suffix...)
	}
	var buf bytes.Buffer
	buf.Grow(len(w.prefix) + len(w.suffix) + 50)
	buf.Write(w.prefix)
	buf.WriteString("\n... omitting ")
	buf.WriteString(strconv.FormatInt(w.skipped, 10))
	buf.WriteString(" bytes ...\n")
	buf.Write(w.suffix[w.suffixOff:])
	buf.Write(w.suffix[:w.suffixOff])
	return buf.Bytes()
}

func minInt(a, b int) int {
	if a < b {
		return a
	}
	return b
}
