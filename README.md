[<img src="https://avatars2.githubusercontent.com/u/24763891?s=400&u=c1150e7da5667f47159d433d8e49dad99a364f5f&v=4"  width="256px" height="256px" align="right" alt="Multiverse OS Logo">](https://github.com/multiverse-os)

## Multiverse OS: `memexec` fileless byte array execution
**URL** [multiverse-os.org](https://multiverse-os.org)

Fileless execution completely in memory execution of binaries without creating 
temporary files or touching the disk is possible using MemoryFD. A rewrite of
the standard library `exec` providing all the same functionality except the
`Command()` function does not take a `path string` but instead takes a `[]byte
binary executable` which is loaded into a memory file descriptor. After this
initial function, everything else has the exact same API.





