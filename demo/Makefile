# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


# Synthesis Makefile for demo

# tcl script
GEN_DEMO_TCL := gen_demo.tcl
GET_PERF_TCL := get_max_clk.tcl

# select the core to use as main processor (defaults to Ibex)
CORE     ?= ibex
CORE_DIR := ../$(CORE)/

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

proj:
	cd $(PROJ_DIR) && vivado -mode batch -source $(abspath $(GEN_DEMO_TCL))   \
	    -tclargs $(abspath ../) $(abspath $(CORE_DIR)) $(PART)                \
	    $(abspath $(CONSTR)) $(abspath $(RAM_FILE)) $(DIFF_CLK) $(CLK_PER)

perf: proj
	cd $(PROJ_DIR) && vivado -mode batch -source $(abspath $(GET_PERF_TCL))   \
	    -tclargs vicuna_demo/vicuna_demo.xpr 80 16 sysclk
