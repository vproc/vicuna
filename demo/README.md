# Demo directory

This directory contains a minimal design for synthesizing the vector processor
on a Xilinx FPGA.  Currently only the NexysVideo and Genesys 2 boards are
supported, but it should be straight forward to port this to any Xilinx FPGA.
The top level module requires only 4 pin connections: a clock signal, a reset
signal, and UART receive and transmit signals.
