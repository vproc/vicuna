# Testing directory

The subdirectories in this directory each contain a set of tests to verify the
correct functionality of the vector processor.  Tests can be executed with the
help of `make`.  The target specified when calling `make` can either be one of
the subdirectories (e.g., `lsu`), in which case all tests in this subdirectory
are executed, a specific test from within a subdirectory (e.g., `alu/vadd_8`),
or `all` (the default target) which runs all the tests (note that this might
take a while).

The default main core used for the tests is
[Ibex](https://github.com/lowRISC/ibex).  This can be changed by setting the
environment variable `CORE`.

The default simulator used for the tests is
[Verilator](https://www.veripool.org/verilator/).  This can be changed by
setting the environment variable `SIMULATOR`.  Currently only Verilator, 
xsim (part of the
[Xilinx Vivado](https://www.xilinx.com/products/design-tools/vivado.html)
suite, set `SIMULATOR` to `vivado` to use it) and Questasim (set `SIMULATOR`
to `questa` to use it) are supported.

By default tracing is disabled in Verilator.  Use the environment variable
`TRACE_VCD` to specify a `*.vcd` file path if you wish to generate a VCD trace
file of a set of tests.  The specified path is relative to the subdirectory of
the respective test set.


## Examples

Run all tests:
```
$ make
```

Run all MUL unit tests:
```
$ make mul
```

Run the simple addition test with a single-element width of 8:
```
$ make alu/vadd_8
```

Run the ELEM tests using [CV32E40X](https://github.com/openhwgroup/cv32e40x)
as the main core instead of Ibex:
```
$ make elem CORE=cv32e40x
```

Run the LSU tests using the `xsim` simulator (part of the Xilinx Vivado suite):
```
$ make lsu SIMULATOR=vivado
```

**Verilator only**:  Run all tests and generate a VCD trace file by using the
variable `TRACE_VCD` or a FST trace file by using the variable `TRACE_FST` for
each test set in the respective subdirectory:
```
$ make TRACE_VCD=trace.vcd
$ make TRACE_FST=trace.fst
```


## Hints

Build files and other intermediate files created while testing (this includes
the entire Vivado project required for simulation with xsim) are saved in a
directory on the temporary file system (`/tmp`) by default.  The environment
variable `PROJ_DIR` can be used to specify an alternative location instead.
For further details, see the [simulation directory](../sim/) (the Makefile of
the simulation directory is invoked for the simulation of the tests).

The build files generated during compilation of the respective tests (see the
[software directory](../sw/) for details on the compilation process) as well as
a small amount of log files and traces of a small subset of signals is created
in the respective test set subdirectory.  These files can be removed with the
command `make clean`.

Note that the simulation log file `sim.log` created in the subdirectory of the
respective set of tests contains the path to the directory where all build and
intermediate files have been created.  Hence, if one wishes to furhter
investigate those files, `head <subdir>/sim.log` can be used to identify that
directory.  In particular, it allows to open the Vivado project from that
directory to further troubleshoot issues with the Vivado GUI.
