Simulation
==========

Vicuna's repository provides scripts for simulation
using `Verilator <https://www.veripool.org/verilator/>`__
(the default, requires version 4.210 or newer),
xsim (the simulator used by `Vivado <https://www.xilinx.com/products/design-tools/vivado.html>`__),
and Questasim.


Getting Started
---------------

Save the following C code to a file called ``test.c``:

.. literalinclude :: ../code/test.c
   :language: c

Compile it with the following command
(replace ``/path/to/vicuna/`` with the path to Vicuna's repository):

.. code-block:: sh

   make -f /path/to/vicuna/sw/Makefile PROG=test OBJ=test.o

This generates an executable file called ``test.elf``
and a memory initialization file called ``test.vmem``.
To troubleshoot compilation issues,
please refer to the :doc:`prerequisites`.

To simulate that program with Verilator,
save the path to the ``test.vmem`` file to a simple text file
and start simulation as follows
(substituting ``/path/to/vicuna/`` with the path to Vicuna's repository):

.. code-block:: sh

   echo "test.vmem" > progs.txt
   make -f /path/to/vicuna/sim/Makefile PROG_PATHS=progs.txt

This should build a simulation model and simulate a single program run,
printing the UART output to the console.

Now, remember those values of the cell you chose
from that table in the :doc:`configuration` section?
Append them to the ``make`` command to simulate a particular configuration of Vicuna.
For instance, if the cell corresponding
to your desired target technology and performance vs area trade-off
contains the values ``VPROC_CONFIG=dual`` and ``VREG_W=512``,
then use the following command:

.. code-block:: sh

   make -f /path/to/vicuna/sim/Makefile PROG_PATHS=progs.txt VPROC_CONFIG=dual VREG_W=512


Simulation Options
------------------

By default, the simulation model is saved to a temporary directory
(created using `mktemp(1) <https://man7.org/linux/man-pages/man1/mktemp.1.html>`__)
and a new model is generated for each simulation run.
You may instead specify a directory for saving the simulation model
with the environment variable ``PROJ_DIR``,
which avoids re-generating the model if the RTL code has not changed
(e.g., append ``PROJ_DIR=/desired/path/to/simulation/model`` to the ``make`` command).

You may specify the desired main core with the environment variable ``CORE``.
Currently, a modified version of `Ibex <https://github.com/lowRISC/ibex>`__ (the default)
or `CV32E40X <https://github.com/openhwgroup/cv32e40x>`__ are supported.
Set ``CORE`` to either ``ibex`` or ``cv32e40x`` to select one of these explicitly
(e.g., append ``CORE=cv32e40x`` to the ``make`` command to use CV32E40X instead of Ibex).


Simulating with Vivado or Questasim
-----------------------------------

While the above instructions use Verilator for simulation,
most of them equally apply to other simulation tools.
The desired simulation tool can be selected by specifying it as target for the ``make`` command.
Allowed values are ``verilator`` (the default), ``vivado``, or ``questa``.
For instance, use the following command to simulate using Vivado's xsim:

.. code-block:: sh

   make -f /path/to/vicuna/sim/Makefile vivado PROG_PATHS=progs.txt ...
