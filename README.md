# Vicuna - a RISC-V Zve32x Vector Coprocessor

Vicuna is an open-source 32-bit integer vector coprocessor written in
SystemVerilog that implements the
[RISC-V "V" extension](https://github.com/riscv/riscv-v-spec)
(presently, the v0.10 draft of the soon-to-be-ratified specification).
The vector core is heavily parametrizable and primarily targets FPGAs,
although patches for ASIC support are welcome.

Vicuna is a coprocessor and thus requires a main processor with a suitable
interface.  Currently, a modified version of the
[Ibex core](https://github.com/lowRISC/ibex) or the
[CV32E40X core](https://github.com/openhwgroup/cv32e40x) serves as the main
core. Support for further RISC-V CPUs is under development.

Vicuna is an integer vector coprocessor and supports element widths of 8, 16,
and 32 bits.  Note that Vicuna currently does not have a floating-point unit
and hence does not support the floating-point vector instructions of the RISC-V
V extension.

Vicuna is under active development, and contributions are welcome!


## Publication

If you use Vicuna in academic work, please cite
[our publication](https://doi.org/10.4230/LIPIcs.ECRTS.2021.1):

```
@InProceedings{platzer_et_al:LIPIcs.ECRTS.2021.1,
  author =  {Platzer, Michael and Puschner, Peter},
  title =   {{Vicuna: A Timing-Predictable RISC-V Vector Coprocessor for Scalable Parallel Computation}},
  booktitle =   {33rd Euromicro Conference on Real-Time Systems (ECRTS 2021)},
  pages =   {1:1--1:18},
  series =  {Leibniz International Proceedings in Informatics (LIPIcs)},
  ISBN =    {978-3-95977-192-4},
  ISSN =    {1868-8969},
  year =    {2021},
  volume =  {196},
  editor =  {Brandenburg, Bj\"{o}rn B.},
  publisher =   {Schloss Dagstuhl -- Leibniz-Zentrum f{\"u}r Informatik},
  address = {Dagstuhl, Germany},
  URL =     {https://drops.dagstuhl.de/opus/volltexte/2021/13932},
  URN =     {urn:nbn:de:0030-drops-139323},
  doi =     {10.4230/LIPIcs.ECRTS.2021.1},
  annote =  {Keywords: Real-time Systems, Vector Processors, RISC-V}
}
```


## Getting Started

This repository uses submodules.  After cloning the repository, run following
command in the top directory to initialize the submodules:
```
git submodule update --init --recursive
```

### Compilation toolchain

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
git clone https://github.com/riscv/riscv-gnu-toolchain -b rvv-intrinsic
cd riscv-gnu-toolchain
git submodule update --init --recursive
mkdir build && cd build
../configure --prefix=/desired/installation/path
make
```

### Simulation

The [`sim/`](https://github.com/vproc/vicuna/tree/main/sim) subdirectory
contains scripts for simulating Vicuna with either
[Verilator](https://www.veripool.org/verilator/) or xsim (the default simulator
in [Vivado](https://www.xilinx.com/products/design-tools/vivado.html)).


### Synthesis

The [`demo/`](https://github.com/vproc/vicuna/tree/main/demo) subdirectory
contains a minimalist demo design for Xilinx FPGAs.


## Configuration

Vicuna allows for extensive parametrization.  In particular, the width of
the vector registers, of the memory interface, and of the datapaths of the
functional units can be configured independently.


## License

Unless otherwise noted, everything in this repository is licensed under the
ISC license, a permissive free software license that is functionally equivalent
to the MIT and the simplified 2-clause BSD license (with some language deemed
unnecessary removed).

The Ibex core (included in this repository as a submodule) is licensed under
the Apache License, see [the Ibex repository](https://github.com/lowRISC/ibex)
for details.

The CV32E40X core (included in this repository as a submodule) is licensed
under the Solderpad Hardware License, see
[the CV32E40X repository](https://github.com/openhwgroup/cv32e40x) for details.
