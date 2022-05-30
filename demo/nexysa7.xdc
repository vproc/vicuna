## This file is a general .xdc for the Nexys A7
## To use it in a project:
## - uncomment the lines corresponding to used pins
## - rename the used ports (in each line, after get_ports) according to the top level signal names in the project

## Clock signal
set_property -dict { PACKAGE_PIN E3    IOSTANDARD LVCMOS33 } [get_ports { sys_clk_pi }]; #IO_L12P_T1_MRCC_35 Sch=clk100mhz
create_clock -period 12.000 -name sysclk [get_ports sys_clk_pi]
set_property CLOCK_DEDICATED_ROUTE BACKBONE [get_nets sys_clk_pi]

##Buttons
set_property -dict { PACKAGE_PIN C12   IOSTANDARD LVCMOS33 } [get_ports { sys_rst_ni }]; #IO_L3P_T0_DQS_AD1P_15 Sch=cpu_resetn

##USB-RS232 Interface
set_property -dict { PACKAGE_PIN C4    IOSTANDARD LVCMOS33 } [get_ports { uart_rx_i }]; #IO_L7P_T1_AD6P_35 Sch=uart_txd_in
set_property -dict { PACKAGE_PIN D4    IOSTANDARD LVCMOS33 } [get_ports { uart_tx_o }]; #IO_L11N_T1_SRCC_35 Sch=uart_rxd_out



