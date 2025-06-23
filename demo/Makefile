# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


# Synthesis Makefile for demo
# requires GNU make; avoid spaces in directory names!

# get the absolute path of the simulation directory (must not contain spaces!)
DEMO_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

# tcl script
GEN_DEMO_TCL := gen_demo.tcl
GET_PERF_TCL := get_max_clk.tcl

# select the core to use as main processor (defaults to Ibex)
CORE     ?= ibex
CORE_DIR := $(DEMO_DIR)/../$(CORE)/

# board and associated part, constraints file and clock info
BOARD  ?= nexysvideo
CONSTR ?= $(BOARD).xdc
ifeq ($(BOARD), nexysvideo)
  PART     ?= xc7a200tsbg484-1
  DIFF_CLK ?= 0
  CLK_PER  ?= 10.0
else
ifeq ($(BOARD), genesys2)
  PART     ?= xc7k325tffg900-2
  DIFF_CLK ?= 1
  CLK_PER  ?= 5.0
else
ifeq ($(BOARD), xc7vx690tffg1157)
  PART     ?= xc7vx690tffg1157-3
  DIFF_CLK ?= 0
  CLK_PER  ?= 20.0
else
ifeq ($(BOARD), nexysa7)
  PART     ?= xc7a100tcsg324-1
  DIFF_CLK ?= 0
  CLK_PER  ?= 10.0
endif
endif
endif
endif

# project target directory
TMP_DIR  := $(shell mktemp -d)
PROJ_DIR ?= $(TMP_DIR)
RAM_FILE ?= demo.vmem

all: proj

# vector coprocessor configuration file generation (defines VMEM_W and VREG_W)
VPROC_CONFIG_PKG := $(PROJ_DIR)/vproc_config.sv
VMEM_W			 := 32
include $(DEMO_DIR)/../config.mk
#from RAM_FILE i have removed the ($abspath $(RAM_FILE)) because it is not needed we will provide always abspath

proj: $(VPROC_CONFIG_PKG)
	cd $(PROJ_DIR) && vivado -mode batch -source $(abspath $(GEN_DEMO_TCL))   \
	    -tclargs $(DEMO_DIR)/../ $(abspath $(CORE_DIR)) $(VPROC_CONFIG_PKG)   \
	    $(PART) $(abspath $(CONSTR))  $(RAM_FILE)                   \
	    $(DIFF_CLK) $(CLK_PER);                                               \
	echo "";                                                                  \
	echo 'Open the project with: $$ vivado $(PROJ_DIR)/vicuna_demo/*.xpr'

perf: proj
	cd $(PROJ_DIR) && vivado -mode batch -source $(abspath $(GET_PERF_TCL))   \
	    -tclargs vicuna_demo/vicuna_demo.xpr 80 16 sysclk
