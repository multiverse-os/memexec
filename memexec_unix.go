// +build !plan9,!windows
package memexec

import (
	"os"
	"syscall"
)

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
