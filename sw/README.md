# Software directory

This directory contains utilities to cross-compile programs to RISC-V for
execution on the vector processor.  It requires a RISC-V compiler with support
for the RISC-V V extension and [SRecord](http://srecord.sourceforge.net/),
which is currently required to convert `*.bin` files to `*.vmem` files due to
[a bug in GNU binutils
](https://github.com/riscv/riscv-tools/issues/168#issuecomment-554973539).


## Compilation toolchain

In order to compile programs for Vicuna, you need a RISC-V compiler which
supports the RISC-V V extension (e.g., LLVM or GCC).  Currently, this extension
is not ratified, and thus only experimental support is available, which is not
included in the official releases.  Therefore, one needs to compile the desired
compilation toolchain with support for the V extension from source.

Execute the following shell commands to compile the RISC-V GNU toolchain with
V extension support enabled.  Note that `/desired/installation/path` should be
replaced with the path where the toolchain should be installed.  Please refer
to the documentation in the
[RISC-V GNU toolchain repository](https://github.com/riscv/riscv-gnu-toolchain#prerequisites)
for the required prerequisites for compiling the toolchain.

```
git clone https://github.com/riscv/riscv-gnu-toolchain
cd riscv-gnu-toolchain
mkdir build && cd build
../configure --prefix=/desired/installation/path
make
```

From the `sw` folder of the Vicuna repository, execute the following command 
to compile LLVM + Clang with V extension support enabled.
Note that `/desired/installation/path` should be
replaced with the path where the toolchain should be cloned to and installed in.
Please refer to the documentation on the
[LLVM Website](https://llvm.org/docs/GettingStarted.html)
for the required prerequisites for compiling the toolchain.

```
make llvm LLVM_DIR=/desired/installation/path
```


## Usage

Compile your program by using the Makefile in this directory and specifying
your program name with the variable `PROG` and object files with `OBJ` (object
files may have `*.c` or `*.S` source files).
Example (note that `/path/to/vicuna/` should be replaced by the path to this
repository):

       make -f /path/to/vicuna/sw/Makefile PROG=test OBJ=test.o
