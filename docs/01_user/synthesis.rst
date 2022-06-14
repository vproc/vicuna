Synthesis
=========

Currently, only synthesis for FPGAs using Vivado is supported.


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

Switch to Vicuna's ``demo/`` subdirectory
and from there execute the following command to generate a Vivado project
for synthesis targeting
`Digilent's Nexys Video <https://digilent.com/reference/programmable-logic/nexys-video/start>`__
board
(note that ``RAM_FILE`` must point to the ``test.vmem`` file generated in the prior step):

.. code-block:: sh

   make RAM_FILE=test.vmem BOARD=nexysvideo

Append configuration values to the command,
such as those listed in the table in the :doc:`configuration` section,
to use a particular configuration of Vicuna.
For instance, if the cell that matches your desired characteristics
contains the values ``VPROC_CONFIG=dual`` and ``VREG_W=512``,
then use the following command:

.. code-block:: sh

   make RAM_FILE=test.vmem BOARD=nexysvideo VPROC_CONFIG=dual VREG_W=512

The last line printed by ``make`` shows the command that can be used to open the Vivado project.
Execute that command and then within Vivado,
click on *Generate Bitstream*
(under section *PROGRAM AND DEBUG* in the flow navigator).
Once the bitstream has been generated,
attach the programming interface of the board to your computer and within Vivado,
open the hardware manager, connect the board, and program it with the generated bitstream.

By default, program output is written to the board's UART at a baud rate of 115200 Hz.
Note that the main core jumps to the reset address whenever the test program terminates,
which causes the program to run again.
Add an infinite loop (e.g., ``while (1) ;``) before the main function's return statement
to run the program only once after reset
(in the test program shown above,
replace ``asm volatile("jr x0");`` with an infinite loop).


Supported Boards
----------------

Use the environment variable ``BOARD`` to select the desired board.
Currently, the following values are allowed:

* ``nexysvideo``: `Digilent's Nexys Video
  <https://digilent.com/reference/programmable-logic/nexys-video/start>`__

* ``genesys2``: `Digilent's Genesys 2
  <https://digilent.com/reference/programmable-logic/genesys-2/start>`__

* ``nexysa7``: `Digilent's Nexys A7
  <https://digilent.com/reference/programmable-logic/nexys-a7/start>`__

If your desired board is not among those listed above,
then you may instead create a constraints file (file extension ``*.xdc``) with following content:

.. code-block:: tcl

   ## Clock Signal
   set_property -dict { PACKAGE_PIN <...> IOSTANDARD <...> } [get_ports { sys_clk_pi }];
   create_clock -period <...> -name sysclk [get_ports sys_clk_pi]
   set_property CLOCK_DEDICATED_ROUTE BACKBONE [get_nets sys_clk_pi]

   ## Buttons
   set_property -dict { PACKAGE_PIN <...> IOSTANDARD <...> } [get_ports { sys_rst_ni }];

   ## UART
   set_property -dict { PACKAGE_PIN <...> IOSTANDARD <...> } [get_ports { uart_tx_o  }];
   set_property -dict { PACKAGE_PIN <...> IOSTANDARD <...> } [get_ports { uart_rx_i  }];

   ## Configuration options
   set_property CONFIG_VOLTAGE <...> [current_design]

Be sure to set the pin numbers, their I/O standards,
the clock period of the system clock,
and the configuration voltage according
to the values corresponding to your board.
Add any additional constraints that might be required
by referring to the documentation of the board.

Then, use the following environment variables to specify your alternative board:

* ``CONSTR``: Path to the constraints ``*.xdc`` file.
* ``PART``: The part name of the FPGA
  (type ``get_parts`` in Vivado's TCL console to get a list of supported part names).
* ``CLK_PER``: The clock period in nanoseconds of the system clock.
* ``DIFF_CLK``: Set to ``1`` if the system clock is differential or ``0`` if it is single-ended.
