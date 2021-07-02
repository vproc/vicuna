# Copyright TU Wien
# Licensed under the ISC license, see LICENSE.txt for details
# SPDX-License-Identifier: ISC

## Clock Signal
set_property -dict { PACKAGE_PIN R4    IOSTANDARD LVCMOS33 } [get_ports { sys_clk_pi }];
create_clock -period 10.000 -name sysclk [get_ports sys_clk_pi]
set_property CLOCK_DEDICATED_ROUTE BACKBONE [get_nets sys_clk_pi]

## Buttons
set_property -dict { PACKAGE_PIN G4    IOSTANDARD LVCMOS15 } [get_ports { sys_rst_ni }];

## UART
set_property -dict { PACKAGE_PIN AA19  IOSTANDARD LVCMOS33 } [get_ports { uart_tx_o  }];
set_property -dict { PACKAGE_PIN V18   IOSTANDARD LVCMOS33 } [get_ports { uart_rx_i  }];

## Configuration options
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
