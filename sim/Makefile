# Copyright TU Wien
# Licensed under the ISC license, see LICENSE.txt for details
# SPDX-License-Identifier: ISC


# Simulations Makefile
# requires GNU make; avoid spaces in directory names!

SHELL := /bin/bash

# get the absolute path of the simulation directory (must not contain spaces!)
SIM_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

# Vivado TCL script
VIVADO_TCL := $(addprefix $(SIM_DIR),sim_vivado.tcl)

# project directory
PROJ_DIR_TMP := $(shell mktemp -d)
PROJ_DIR     ?= $(PROJ_DIR_TMP)

# main core directory (Ibex by default)
CORE_DIR ?= $(SIM_DIR)/../ibex/

# memory files
PROG_PATHS_LIST ?= progs.csv

# trace file
TRACE_FILE ?= sim_trace.csv
TRACE_SIGS ?= '*'

# select width of vector registers, vector memory, and multiplier in bits
VREG_W ?= 128
VMEM_W ?= 32
VMUL_W ?= 64
VALU_W ?= $(VMUL_W)
VSLD_W ?= $(if $(filter-out 32,$(VMUL_W)),$(VMUL_W),64)

# set configuration of instruction and data caches (both disabled by default)
ICACHE_SZ     ?= 0
ICACHE_LINE_W ?= 128
DCACHE_SZ     ?= 0
DCACHE_LINE_W ?= $$(($(VMEM_W) * 2))

# select memory width (bits), size (bytes), and latency (cycles, 1 is minimum)
MEM_W		?= 32
MEM_SZ      ?= 262144
MEM_LATENCY ?= 1

vivado:
	cd $(PROJ_DIR) && vivado -mode batch -source $(VIVADO_TCL)                \
	    -tclargs $(SIM_DIR)/../ $(CORE_DIR) "VREG_W=$(VREG_W)                 \
	    VMEM_W=$(VMEM_W) VMUL_W=$(VMUL_W) VALU_W=$(VALU_W) VSLD_W=$(VSLD_W)   \
	    ICACHE_SZ=$(ICACHE_SZ) ICACHE_LINE_W=$(ICACHE_LINE_W)                 \
	    DCACHE_SZ=$(DCACHE_SZ) DCACHE_LINE_W=$(DCACHE_LINE_W)                 \
	    MEM_W=$(MEM_W) MEM_SZ=$(MEM_SZ) MEM_LATENCY=$(MEM_LATENCY)"           \
	    $(abspath $(TRACE_FILE)) $(abspath $(PROG_PATHS_LIST)) $(TRACE_SIGS)

verilator:
	cp $(SIM_DIR)/verilator_main.cpp $(PROJ_DIR)/
	cd $(PROJ_DIR);                                                           \
	trace="";                                                                 \
	cflags="";                                                                \
	if [[ "$(TRACE_VCD)" != "" ]]; then                                       \
	    trace="--trace";                                                      \
	    cflags="-CFLAGS -DTRACE_VCD";                                         \
	elif [[ "$(TRACE_FST)" != "" ]]; then                                     \
	    trace="--trace-fst";                                                  \
	    cflags="-CFLAGS -DTRACE_FST";                                         \
	fi;                                                                       \
	version=`verilator --version | awk '{print $$2}'`;                        \
	if [ `printf '4.210\n%s\n' "$$version" | sort -V | head -n1` = "4.210" ]; \
	then                                                                      \
	    cflags="$$cflags -CFLAGS -DVERILATOR_4_210";                          \
	fi;                                                                       \
	core="";                                                                  \
	inc="";                                                                   \
	src="";                                                                   \
	if echo "$(CORE_DIR)" | grep -q "ibex"; then                              \
	    core="-DMAIN_CORE_IBEX";                                              \
	    inc="-I$(CORE_DIR)/rtl/ -I$(CORE_DIR)/dv/uvm/core_ibex/common/prim/"; \
	    inc="$$inc -I$(CORE_DIR)/vendor/lowrisc_ip/dv/sv/dv_utils/";          \
	    inc="$$inc -I$(CORE_DIR)/vendor/lowrisc_ip/ip/prim/rtl/";             \
	    inc="$$inc -I$(CORE_DIR)/vendor/lowrisc_ip/ip/prim_generic/rtl/";     \
	    src="ibex_pkg.sv prim_pkg.sv prim_assert.sv prim_ram_1p_pkg.sv";      \
	    src="$$src ibex_register_file_ff.sv";                                 \
	elif echo "$(CORE_DIR)" | grep -q "cv32e40x"; then                        \
	    core="-DMAIN_CORE_CV32E40X";                                          \
	    inc="-I$(CORE_DIR)/rtl/ -I$(CORE_DIR)/rtl/include/";                  \
	    inc="$$inc -I$(CORE_DIR)/bhv/";                                       \
	    src="cv32e40x_pkg.sv if_xif.sv if_c_obi.sv";                          \
	    src="$$src cv32e40x_sim_clock_gate.sv";                               \
	fi;                                                                       \
	verilator --unroll-count 1024 -Wno-WIDTH -Wno-PINMISSING -Wno-UNOPTFLAT   \
	    -Wno-UNSIGNED -Wno-IMPLICIT -Wno-LITENDIAN -Wno-CASEINCOMPLETE        \
	    -Wno-SYMRSVDWORD -Wno-BLKANDNBLK -Wno-BLKSEQ -Wno-SYNCASYNCNET        \
	    -I$(SIM_DIR)/../rtl/ -I$(SIM_DIR)/../sva/ $$inc $$core                \
	    -GMEM_W=$(MEM_W) -GVREG_W=$(VREG_W) -GVMEM_W=$(VMEM_W)                \
	    -GVMUL_W=$(VMUL_W) -GVALU_W=$(VALU_W) -GVSLD_W=$(VSLD_W)              \
	    -GICACHE_SZ=$(ICACHE_SZ) -GICACHE_LINE_W=$(ICACHE_LINE_W)             \
	    -GDCACHE_SZ=$(DCACHE_SZ) -GDCACHE_LINE_W=$(DCACHE_LINE_W)             \
	    --cc $$src vproc_pkg.sv vproc_top.sv vproc_hazards.sv                 \
	    vproc_vregpack.sv vproc_vregunpack.sv --top-module vproc_top          \
	    --clk clk_i $$trace $$cflags --exe verilator_main.cpp;                \
	if [ "$$?" != "0" ]; then                                                 \
	    exit 1;                                                               \
	fi;                                                                       \
	make -C $(PROJ_DIR)/obj_dir -f Vvproc_top.mk Vvproc_top;                  \
	$(PROJ_DIR)/obj_dir/Vvproc_top $(abspath $(PROG_PATHS_LIST)) $(MEM_W)     \
	    $(MEM_SZ) $(MEM_LATENCY) $$(($(VREG_W) * 2)) $(abspath $(TRACE_FILE)) \
	    $(abspath $(TRACE_VCD)) $(abspath $(TRACE_FST))
