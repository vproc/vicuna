# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


# Makefile for generating the configuration package
#
# The intent of the dynamically generated configuration package is to provide
# *consistent default values* for configuration parameters of the vproc_core
# module across different synthesis and simulation workflows.
#
# The configuration is controlled with following (environment) variables:
#  - VMEM_W: The width (in bits) of the vector coprocessor's memory interface
#  - VREG_W: The width (in bits) of the vector coprocessor's vector registers
#  - VPROC_PIPELINES: Defines the vector pipelines. Each pipeline is defined by
#    a string of the form "WIDTH:UNIT[,UNIT]*" where WIDTH is the width in bits
#    of the pipeline's datapath and each occurence of UNIT selects one of the
#    vector execution units (either VLSU, VALU, VMUL, VSLD, or VELEM).
#  - VPROC_CONFIG: Sets default values for the other parameters (that can be
#    individually overriden) depending on the desired number of vector
#    pipelines (choose 1, 2, 3, or 5 pipelines by setting this variable to
#    compact, dual, triple, or legacy, respectively).

VPROC_CONFIG_PKG ?= vproc_config.sv

VPROC_CONFIG ?= compact
ifeq ($(VPROC_CONFIG), compact)
  VPORT_POLICY    ?= some
  VMEM_W          ?= 32
  VREG_W          ?= 128
  VPROC_PIPELINES ?= $(VMEM_W):VLSU,VALU,VMUL,VSLD,VELEM
else
ifeq ($(VPROC_CONFIG), dual)
  VPORT_POLICY    ?= some
  VMEM_W          ?= 32
  VREG_W          ?= 128
  VPROC_PIPELINES ?= $(VMEM_W):VLSU,VALU,VELEM $(VPIPE_W_VMUL):VMUL,VSLD
else
ifeq ($(VPROC_CONFIG), triple)
  VPORT_POLICY    ?= some
  VMEM_W          ?= 32
  VREG_W          ?= 256
  VPROC_PIPELINES ?= $(VMEM_W):VLSU $(VPIPE_W_DFLT):VALU,VELEM $(VPIPE_W_VMUL):VMUL,VSLD
else
ifeq ($(VPROC_CONFIG), legacy)
  VPORT_POLICY    ?= some
  VMEM_W          ?= 32
  VREG_W          ?= 128
  VPROC_PIPELINES ?= $(VMEM_W):VLSU $(VPIPE_W_DFLT):VALU $(VPIPE_W_VMUL):VMUL                     \
                                    $(VPIPE_W_DFLT):VSLD 32:VELEM
else
$(error Unknown vector coprocessor configuration $(VPROC_CONFIG))
endif
endif
endif
endif

# default widths of vector pipelines based on VPORT_POLICY
ifeq ($(VPORT_POLICY), few)
  VPIPE_W_DFLT := $(shell echo $$(($(VREG_W) / 2)))
  VPIPE_W_VMUL := $(shell echo $$(($(VREG_W) / 4)))
else
ifeq ($(VPORT_POLICY), some)
  VPIPE_W_DFLT := $(shell echo $$(($(VREG_W) / 2)))
  VPIPE_W_VMUL := $(shell echo $$(($(VREG_W) / 2)))
else
ifeq ($(VPORT_POLICY), many)
  VPIPE_W_DFLT := $(VREG_W)
  VPIPE_W_VMUL := $(VREG_W)
else
$(error Unknown vector register file port policy $(VPORT_POLICY))
endif
endif
endif

.PHONY: $(VPROC_CONFIG_PKG)
$(VPROC_CONFIG_PKG):
	@echo "// Auto-generated on $$(date)"                                                    >$@; \
	echo ""                                                                                 >>$@; \
	echo "// Vector coprocessor default configuration package"                              >>$@; \
	echo "//"                                                                               >>$@; \
	echo "// The package defined in this file provides *consistent default values* for"     >>$@; \
	echo "// configuration parameters of the vproc_core module for the configuration"       >>$@; \
	echo "// shown below across different synthesis and simulation workflows. The"          >>$@; \
	echo "// constants defined in this package are intended to be used *exclusively* as"    >>$@; \
	echo "// *default values* for the parameters of the vproc_core module and should"       >>$@; \
	echo "// *not* be used anywhere else in the code, such that a design instantiating"     >>$@; \
	echo "// the vproc_core module can override any parameter with a different value."      >>$@; \
	echo ""                                                                                 >>$@; \
	echo "// Configuration details:"                                                        >>$@; \
	echo "// - Vector register width: $(VREG_W) bits"                                       >>$@; \
	echo "// - Vector pipelines:"                                                           >>$@; \
	vport_rd_cnt=1;                                                                               \
	vport_wr_capacities="";                                                                       \
	pipe_cnt=0;                                                                                   \
	pipe_units="";                                                                                \
	pipe_widths="";                                                                               \
	pipe_vport_cnt="";                                                                            \
	pipe_vport_idx="";                                                                            \
	pipe_vport_wr="";                                                                             \
	for pipe in $(VPROC_PIPELINES); do                                                            \
	    width=`echo $$pipe | cut -d ":" -f 1`;                                                    \
	    unit_str=`echo $$pipe | cut -d ":" -f 2 | sed 's/,/, /g'`;                                \
	    unit_mask=`echo $$pipe | cut -d ":" -f 2 | sed 's/,/ | /g' |                              \
	               sed "s/V\(LSU\|ALU\|MUL\|SLD\|ELEM\)/(UNIT_CNT'(1) << UNIT_\1)/g"`;            \
	    vport_cnt=1;                                                                              \
	    if echo "$$pipe" | grep -q "VMUL" && [ $$(($$width * 4)) -gt "$(VREG_W)" ]; then          \
	        vport_cnt=2;                                                                          \
	    fi;                                                                                       \
	    if [ $$(($$width * 2)) -gt "$(VREG_W)" ]; then                                            \
	        vport_cnt=$$(($$vport_cnt + 1));                                                      \
	    fi;                                                                                       \
	    vport_wr=0;                                                                               \
	    remaining_cap=$$(($(VREG_W) - $$width));                                                  \
	    for cap in $$(echo $$vport_wr_capacities); do                                             \
	        if [ "$$cap" -ge "$$width" ]; then                                                    \
	            remaining_cap=$$(($$cap - $$width));                                              \
	            break;                                                                            \
	        fi;                                                                                   \
	        vport_wr=$$(($$vport_wr + 1));                                                        \
	    done;                                                                                     \
	    if [ -z "$$pipe_units" ]; then                                                            \
	        pipe_units="$${unit_mask}";                                                           \
	        pipe_widths="$${width}";                                                              \
	        pipe_vport_cnt="$${vport_cnt}";                                                       \
	        pipe_vport_idx="$${vport_rd_cnt}";                                                    \
	        pipe_vport_wr="$${vport_wr}";                                                         \
	    else                                                                                      \
	        pipe_units="$${pipe_units}, $${unit_mask}";                                           \
	        pipe_widths="$${pipe_widths}, $${width}";                                             \
	        pipe_vport_cnt="$${pipe_vport_cnt}, $${vport_cnt}";                                   \
	        pipe_vport_idx="$${pipe_vport_idx}, $${vport_rd_cnt}";                                \
	        pipe_vport_wr="$${pipe_vport_wr}, $${vport_wr}";                                      \
	    fi;                                                                                       \
	    vport_rd_cnt=$$(($$vport_rd_cnt + $$vport_cnt));                                          \
	    if [ "$$vport_wr" = `echo $${vport_wr_capacities} | wc -w` ]; then                        \
	        vport_wr_capacities="$${vport_wr_capacities} $${remaining_cap}";                      \
	    else                                                                                      \
	        awk_word_idx=$$(($$vport_wr + 1));                                                    \
	        vport_wr_capacities=`echo "$${vport_wr_capacities}" |                                 \
	                             awk -v n=$$awk_word_idx -v r=$$remaining_cap '{$$n=r} 1'`;       \
	    fi;                                                                                       \
	    echo "//   * Pipeline $${pipe_cnt}: $${width} bits wide, contains $${unit_str}"     >>$@; \
	    echo "//     Uses $${vport_cnt} $(VREG_W)-bit vreg read ports"                            \
	         "and write port $${vport_wr}"                                                  >>$@; \
	    pipe_cnt=$$(($$pipe_cnt + 1));                                                            \
	done;                                                                                         \
	pipe_widths="'{$${pipe_widths}}";                                                             \
	pipe_vport_cnt="'{$${pipe_vport_cnt}}";                                                       \
	pipe_vport_idx="'{$${pipe_vport_idx}}";                                                       \
	pipe_vport_wr="'{$${pipe_vport_wr}}";                                                         \
	vport_wr_cnt=`echo $${vport_wr_capacities} | wc -w`;                                          \
	echo "// - Vector register file needs $${vport_rd_cnt} read ports and $${vport_wr_cnt}"       \
	     "write ports"                                                                      >>$@; \
	buf_flags="(BUF_FLAGS_W'(1) << BUF_DEQUEUE) | (BUF_FLAGS_W'(1) << BUF_VREG_PEND)";            \
	if [ -n "$(TIMEPRED)" ] && [ "$(TIMEPRED)" != "0" ]; then                                     \
	    buf_flags="$${buf_flags} | (BUF_FLAGS_W'(1) << BUF_VREG_WR_MUX_TIMEPRED)";                \
	fi;                                                                                           \
	echo ""                                                                                 >>$@; \
	echo "package vproc_config;"                                                            >>$@; \
	echo ""                                                                                 >>$@; \
	echo "    import vproc_pkg::*;"                                                         >>$@; \
	echo ""                                                                                 >>$@; \
	echo "    parameter vreg_type    VREG_TYPE                   = VREG_GENERIC;"           >>$@; \
	echo "    parameter int unsigned VREG_W                      = $(VREG_W);"              >>$@; \
	echo "    parameter int unsigned VPORT_RD_CNT                = $$vport_rd_cnt;"         >>$@; \
	echo "    parameter int unsigned VPORT_RD_W   [VPORT_RD_CNT] = '{default: VREG_W};"     >>$@; \
	echo "    parameter int unsigned VPORT_WR_CNT                = $$vport_wr_cnt;"         >>$@; \
	echo "    parameter int unsigned VPORT_WR_W   [VPORT_WR_CNT] = '{default: VREG_W};"     >>$@; \
	echo ""                                                                                 >>$@; \
	echo "    parameter int unsigned PIPE_CNT                    = $$pipe_cnt;"             >>$@; \
	echo "    parameter bit [UNIT_CNT-1:0] PIPE_UNITS [PIPE_CNT] = '{"                      >>$@; \
	echo "        $$pipe_units"                                                             >>$@; \
	echo "    };"                                                                           >>$@; \
	echo "    parameter int unsigned PIPE_W           [PIPE_CNT] = $$pipe_widths;"          >>$@; \
	echo "    parameter int unsigned PIPE_VPORT_CNT   [PIPE_CNT] = $$pipe_vport_cnt;"       >>$@; \
	echo "    parameter int unsigned PIPE_VPORT_IDX   [PIPE_CNT] = $$pipe_vport_idx;"       >>$@; \
	echo "    parameter int unsigned PIPE_VPORT_WR    [PIPE_CNT] = $$pipe_vport_wr;"        >>$@; \
	echo ""                                                                                 >>$@; \
	echo "    parameter int unsigned VLSU_QUEUE_SZ               = 4;"                      >>$@; \
	echo "    parameter bit [VLSU_FLAGS_W-1:0] VLSU_FLAGS        = '0;"                     >>$@; \
	echo "    parameter mul_type     MUL_TYPE                    = MUL_GENERIC;"            >>$@; \
	echo ""                                                                                 >>$@; \
	echo "    parameter int unsigned INSTR_QUEUE_SZ              = 2;"                      >>$@; \
	echo "    parameter bit [BUF_FLAGS_W-1:0] BUF_FLAGS          = $${buf_flags};"          >>$@; \
	echo ""                                                                                 >>$@; \
	echo "endpackage"                                                                       >>$@;
