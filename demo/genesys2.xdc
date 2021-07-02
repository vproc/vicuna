# Copyright TU Wien
# Licensed under the ISC license, see LICENSE.txt for details
# SPDX-License-Identifier: ISC


## Clock Signal
set_property -dict { PACKAGE_PIN AD11  IOSTANDARD LVDS     } [get_ports { sys_clk_ni }];
set_property -dict { PACKAGE_PIN AD12  IOSTANDARD LVDS     } [get_ports { sys_clk_pi }];
create_clock -period 5.000 -name sysclk [get_ports sys_clk_pi]
set_property CLOCK_DEDICATED_ROUTE BACKBONE [get_nets sys_clk_pi]

## Buttons
set_property -dict { PACKAGE_PIN R19   IOSTANDARD LVCMOS33 } [get_ports { sys_rst_ni }];

## UART
set_property -dict { PACKAGE_PIN Y23   IOSTANDARD LVCMOS33 } [get_ports { uart_tx_o  }];
set_property -dict { PACKAGE_PIN Y20   IOSTANDARD LVCMOS33 } [get_ports { uart_rx_i  }];

## Configuration options
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
