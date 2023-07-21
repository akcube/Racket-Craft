# RacketCraft
A Racket implementation of a nanopass compiler for (a subset of) Racket to x86asm

## [Public student code](https://github.com/IUCompilerCourse/public-student-support-code)

Utility code, test suites, etc. for the [compiler course](https://github.com/IUCompilerCourse/Essentials-of-Compilation). This code will be described in the Appendix of the book. The `runtime.c` file needs to be compiled and linked with the assembly code that your compiler produces. To compile `runtime.c`, do the following
```
   gcc -c -g -std=c99 runtime.c
```
This will produce a file named `runtime.o`. The -g flag is to tell the compiler to produce debug information that you may need to use the gdb (or lldb) debugger.

Next, suppose your compiler has translated the Racket program in file `foo.rkt` into the x86 assembly program in file `foo.s` (The .s filename extension is the standard one for assembly programs.) To produce an executable program, you can then do
```
  gcc -g runtime.o foo.s
```
which will produce the executable program named a.out.

## Personal Notes - Adding compiler tests

1. Add a `.rkt` test file in `/tests`, e.g.
```
; /tests/var_test_1.rkt
(let ([x (read)])
  (+ x 1))
```
2. Add a `.in` file containing inputs to all the `read` calls, e.g.
```
; /tests/var_test_1.in
5
```
3. Add a `.res` file containingt the expected output, e.g.
```
; /test/var_test_1.res
6
```
4. Tests are run with the `run-tests.rkt` module. You can run these tests either from the command
line with:
```
racket run-tests.rkt
```
Or by opening and running `run-tests.rkt` in DrRacket.
Before running the compiler tests, you need to compile `runtime.c` (see above).

## Personal notes - Running GDB

1. Compile the `.s` file with `-g` to generate debugging symbols for gdb
```
  gcc -g var_test_11.s
```
2. Run the process via gdb using
```
  gdb var_test_11.out
```
3. You can set break points by passing addresses via `<label> + <offset>`, e.g.
```
  (gdb) info break
  No breakpoints or watchpoints.
  (gdb) break *main+2
  Breakpoint 1 at 0x1124: file var_test_1.s, line 8.
```
4. Now my personal favorite, use `tui enable` to launch into the text user interface of gdb. Now press `Ctrl + X`, followed by `2`. Doing this will cycle through the different viewing modes. The second mode exposes each line of generated assembly to you and you can `stepi` to step through it instruction by instruction. The 3rd mode is a split view between asm and register states. Use as per your liking. 
5. Use `info frame` to show stack frame info and `x/<offset><bxd><bhwg> <addr>` to examine contents at that address, e.g.
```
   (gdb) x/4xw $sp
```
prints "four words (`w`) of memory above the stack pointer (here, `$sp`) in hexadecimal (`x`)".
