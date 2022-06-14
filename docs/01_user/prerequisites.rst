Prerequisites
=============

In order to compile programs for Vicuna,
you need a compilation toolchain with support for the RISC-V vector extension.
It is recommended to use LLVM 14+,
but a GCC 12+ cross-compiler for bare-metal RISC-V should work as well.
Additionally, depending on your needs
a simulation and/or synthesis tool with support for SystemVerilog is required.
Note that for Verilator the minimum version is 4.210.


TL;DR
-----

On Ubuntu 22.04, execute the following commands and you are good to go.

.. literalinclude :: ../code/ubuntu_22_04_quickstart.sh
   :language: sh
   :start-at: sudo

While these commands are executing
you might want to have a look at the :doc:`configuration` section
and try to figure out which configuration of Vicuna you want to use.


RISC-V compilation toolchain
----------------------------

Support for the RISC-V vector extension is available starting with LLVM 14 and GCC 12.
LLVM 14+ is the recommended compilation toolchain.
If it is not available for your distribution,
then it can be compiled from source by executing following command
in the ``sw/`` subdirectory of Vicuna's repository
(note that ``/desired/installation/path`` should be replaced
with the path where you wish to install LLVM):

.. code-block:: sh

   make llvm LLVM_DIR=/desired/installation/path

In addition, the `SRecord package <http://srecord.sourceforge.net/>`__ is required
to generate memory initialization files for simulation and synthesis.
This should be available as a package for most distributions.

To check whether everything is set up correctly,
you might want to try compiling a short test program:

.. literalinclude :: ../code/test.c
   :language: c

Save the C code above to a file called ``test.c`` and,
from the directory where that file is located,
execute the following command to compile it
(note that ``/path/to/vicuna/`` should be substituted with the path to Vicuna's repository):

.. code-block:: sh

   make -f /path/to/vicuna/sw/Makefile PROG=test OBJ=test.o

The environment variable ``COMPILER``
can be set to either ``llvm`` (the default) or ``gcc``
to explicitely select the corresponding compiler
(e.g., append ``COMPILER=gcc`` to the command to use GCC instead of LLVM).

If your environment is set up correctly,
this will first compile and link the test program to an executable called ``test.elf``,
then use ``objcopy`` (or ``llvm-objcopy``) and ``srec_cat`` to convert the ``*.elf`` file
to a memory initialization file called ``test.vmem``.

If you get an error related to the architecture name
(e.g., ``invalid arch name 'rv32imzve32x'`` or similar),
then the compiler that you are using does not support the RISC-V V extension.
Note that the directory where the binaries of a suitable RISC-V compiler are located
must be listed in your ``PATH`` environment variable.
Use the command ``echo $PATH`` to check whether that is the case
and the following command to add that directory if it is still missing
(note that ``/path/to/riscv/compiler/`` must be replaced by the directory
where the binaries of a suitable compilation toolchain are located):

.. code-block:: sh

   export PATH=/path/to/riscv/compiler/:$PATH

A different program name than ``test`` may be selected
by changing the value of the ``PROG`` variable passed to the ``sw/`` Makefile
and further source files can be added by extending the list of object files passed to ``OBJ``.
For instance, a program called ``vector``
comprising the source files ``direction.c`` and ``magnitude.S`` may be compiled as follows:

.. code-block:: sh

   make -f /path/to/vicuna/sw/Makefile PROG=vector OBJ="direction.o magnitude.o"


Supported simulation tools
--------------------------

Verilator is the default tool for simulating Vicuna.
However, the minimum required version is 4.210,
which at the time of writing has not yet been packaged for many popular distributions.
If Verilator 4.210 is not available for your distribution,
it must be compiled from source
by following `the instructions in Verilator's documentation
<https://verilator.org/guide/latest/install.html#git-quick-install>`__.

In addition, simulation scripts are provided for
Vivado's simulator ``xsim``
and for Questasim.


Supported synthesis tools
-------------------------

Currently, only synthesis using Vivado is supported.
