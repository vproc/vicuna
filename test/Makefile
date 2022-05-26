# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


# Tests Makefile
# requires GNU make; avoid spaces in directory names!

SHELL := /bin/bash

# get the absolute path of the test directory (must not contain spaces!)
TEST_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

# select the core to use as main processor (defaults to Ibex)
CORE     ?= ibex
CORE_DIR := $(TEST_DIR)/../$(CORE)/

# select the simulator to use; either verilator (default) or vivado
SIMULATOR ?= verilator

# select the compiler to use; either gcc (default) or llvm
COMPILER ?= gcc

# test directories
TEST_DIRS := lsu alu mul sld elem csr kernel misc

# test targets
TESTS_ALL := $(TEST_DIRS) $(addsuffix /, $(TEST_DIRS))
TESTS_ALL := $(TESTS_ALL) $(basename $(shell find $(TEST_DIRS) -name '*.S'))


.PHONY: all $(TESTS_ALL)
all: $(TESTS_ALL)


# TODO find ways to check that:
# - all parameters are initialized
lint: lint-verible

# Verible Linting Rules
# change rule parameters
LINT_VERIBLE := typedef-structs-unions=allow_anonymous_nested:true
LINT_VERIBLE := $(LINT_VERIBLE),parameter-name-style=localparam_style:ALL_CAPS
LINT_VERIBLE := $(LINT_VERIBLE),line-length=length:200
# enable rules
LINT_VERIBLE := $(LINT_VERIBLE),proper-parameter-declaration
LINT_VERIBLE := $(LINT_VERIBLE),signal-name-style
# disable rules
LINT_VERIBLE := $(LINT_VERIBLE),-generate-label,-struct-union-name-style
LINT_VERIBLE := $(LINT_VERIBLE),-explicit-parameter-storage-type
LINT_VERIBLE := $(LINT_VERIBLE),-undersized-binary-literal
LINT_VERIBLE := $(LINT_VERIBLE),-interface-name-style
lint-verible:
	verible-verilog-lint --rules="$(LINT_VERIBLE)"                            \
	    `ls $(TEST_DIR)/../rtl/*.sv | grep -v vproc_pkg.sv`

lint-verilator:
	verilator -Wall -Wno-PINCONNECTEMPTY -Wno-UNUSED -Wno-UNDRIVEN            \
		-Wno-UNSIGNED -Wno-DECLFILENAME -Wno-USERFATAL -Wno-SYNCASYNCNET      \
	    -I$(TEST_DIR)/../rtl/ --cc vproc_pkg.sv vproc_config.sv vproc_top.sv  \
	    vproc_xif.sv vproc_core.sv vproc_vregpack.sv vproc_vregunpack.sv      \
	    --top-module vproc_top --clk clk_i --lint-only


.SECONDEXPANSION:
$(TESTS_ALL): %: $$(addsuffix .vmem,$$(basename $$(shell [ -d % ] && ls %/*.S || ls %.S)))
	@if [[ -d $@ ]]; then                                                     \
	    cd $@;                                                                \
	else                                                                      \
	    cd $(dir $@);                                                         \
	fi;                                                                       \
	rm -f progs.txt;                                                          \
	test_vmems=($(abspath $^));                                               \
	for memi in "$${test_vmems[@]}"; do                                       \
	    elf="$${memi%.*}.elf";                                                \
	    vref_start=`readelf -s $$elf | grep vref_start |                      \
	                sed 's/^.*\([A-Fa-f0-9]\{8\}\).*$$/\1/'`;                 \
	    vref_end=`readelf -s $$elf | grep vref_end |                          \
	              sed 's/^.*\([A-Fa-f0-9]\{8\}\).*$$/\1/'`;                   \
	    vdata_start=`readelf -s $$elf | grep vdata_start |                    \
	                 sed 's/^.*\([A-Fa-f0-9]\{8\}\).*$$/\1/'`;                \
	    vdata_end=`readelf -s $$elf | grep vdata_end |                        \
	               sed 's/^.*\([A-Fa-f0-9]\{8\}\).*$$/\1/'`;                  \
	    memref="$${memi%.*}.ref.vmem $$vref_start $$vref_end";                \
	    memo="$${memi%.*}.dump.vmem $$vdata_start $$vdata_end";               \
	    echo "$$memi $$memref $$memo " >> progs.txt;                          \
	done;                                                                     \
	retval=0;                                                                 \
	while IFS= read -ra line; do                                              \
	    if [[ "$$line" == "" ]] || [[ "$$line" == \#* ]]; then                \
	        continue;                                                         \
	    fi;                                                                   \
	    printf "\033[0;34m[CONF]\033[0;0m $@ $$line\n";                       \
	    sim_dir=`mktemp -d`;                                                  \
	    echo "[INFO] Writing temporary files to $${sim_dir}";                 \
	    make -f $(TEST_DIR)/../sim/Makefile $(SIMULATOR) PROJ_DIR=$$sim_dir   \
	        $$line PROG_PATHS_LIST=progs.txt CORE_DIR=$(CORE_DIR) ENABLE_SVA=1\
	        TRACE_SIGS="`cat $(TEST_DIR)/trace-sigs.conf`" >sim.log 2>&1;     \
	    if [ "$$?" != "0" ]; then                                             \
	        printf "\033[0;31m[FAIL]\033[0;0m $@ simulation error; ";         \
	        printf "last 10 lines of log file $@/sim.log:\n";                 \
	        tail -n 10 sim.log;                                               \
	        echo "";                                                          \
	        echo "[INFO] View full log with: $$ less $(abspath $@/sim.log)";  \
	        if [ "$(SIMULATOR)" == "vivado" ]; then                           \
				xpr_path="$${sim_dir}/vproc_sim/vproc_sim.xpr";               \
			    echo "[INFO] View waveform with: $$ vivado $${xpr_path}";     \
	        elif [ "$(SIMULATOR)" == "questa" ]; then                         \
				wlf_path="$${sim_dir}/vsim.wlf";                              \
				echo "[INFO] View waveform with: $$ vsim -view $${wlf_path}"; \
	        fi;                                                               \
	        exit 1;                                                           \
	    fi;                                                                   \
	    pend_vreg_wr_col=`head -n 1 sim_trace.csv | sed 's/;/\n/g' |          \
	                      grep -n pend_vreg_wr_map_o |                        \
	                      awk -F ':' '{print $$1}' | head -n 1`;              \
	    if [[ "$$pend_vreg_wr_col" =~ ^[0-9]+$$ ]]; then                      \
	        hazards=`tail -n 1 sim_trace.csv |                                \
	                 awk -F ';' -v idx="$$pend_vreg_wr_col" '{print $$idx}'`; \
	        if [ "$$hazards" != "00000000" ]; then                            \
	            printf "\033[0;33m[WARN]\033[0;0m $@ ";                       \
	            printf "uncleared write hazard(s) (0x$${hazards})\n";         \
	        fi;                                                               \
	    else                                                                  \
	        printf "\033[0;33m[WARN]\033[0;0m $@ ";                           \
	        printf "write hazards are not among traced signals\n";            \
	    fi;                                                                   \
	    rst_col=`head -n 1 sim_trace.csv | sed 's/;/\n/g' | grep -n rst_ni |  \
	             awk -F ':' '{print $$1}' | head -n 1`;                       \
	    t_start=();                                                           \
	    t_end=();                                                             \
	    expected=0;                                                           \
	    while IFS= read -r t_reset; do                                        \
	        if [[ $$expected != 0 ]] && [[ $$expected != $$t_reset ]]; then   \
	            t_start+=($$expected);                                        \
	            t_end+=($$t_reset);                                           \
	        fi;                                                               \
	        expected=$$(($$t_reset + 1));                                     \
	    done < <(awk -F ';' -v idx="$$rst_col" '{print $$idx}' sim_trace.csv |\
	             grep -n 0 | awk -F ':' '{print $$1}');                       \
	    t_start+=($$expected);                                                \
	    t_end+=(`wc -l sim_trace.csv | awk '{print $$1}'`);                   \
	    idx=0;                                                                \
	    for memi in "$${test_vmems[@]}"; do                                   \
	        prog_cycles=$$(($${t_end[$$idx]} - $${t_start[$$idx]}));          \
	        perf_info=`printf '%9s cycles (%9s - %9s)' $$prog_cycles          \
	                   $${t_start[$$idx]} $${t_end[$$idx]}`;                  \
	        prog_name="$$(basename $${memi%.*})";                             \
	        memref="$${memi%.*}.ref.vmem";                                    \
	        memo="$${memi%.*}.dump.vmem";                                     \
	        memdiff=`diff -u $$memref $$memo`;                                \
	        if [ "$$?" != "0" ]; then                                         \
	            printf '\033[0;31m[FAIL]\033[0;0m %-30s %s\n' $@/$$prog_name  \
				    "$$perf_info";                                            \
	            echo "incorrect memory content; diff:";                       \
	            echo "$$memdiff";                                             \
	            retval=1;                                                     \
	        else                                                              \
	            printf '\033[0;32m[PASS]\033[0;0m %-30s %s\n' $@/$$prog_name  \
	                "$$perf_info";                                            \
	        fi;                                                               \
	        idx=$$(($$idx + 1));                                              \
	    done;                                                                 \
	done < test_configs.conf;                                                 \
	exit $$retval


%.vmem: %.S $(TEST_DIR)/spill_cache.S
	@cd $(dir $@);                                                            \
	prog=$(abspath $(<:%.S=%));                                               \
	obj="$(abspath $(^:%.S=%.o))";                                            \
	log="$${prog}_build.log";                                                 \
	make -f $(TEST_DIR)/../sw/Makefile PROG=$$prog OBJ="$$obj"                \
	COMPILER=$(COMPILER) >$$log 2>&1;                                         \
	if [ "$$?" != "0" ]; then                                                 \
	    printf "\033[0;31m[FAIL]\033[0;0m $@ build error; log file $$log:\n"; \
	    cat $$log;                                                            \
	    exit 1;                                                               \
	fi


clean:
	rm -f  $(addsuffix /*.o,$(TEST_DIRS))
	rm -f  $(addsuffix /*.elf,$(TEST_DIRS))
	rm -f  $(addsuffix /*.bin,$(TEST_DIRS))
	rm -f  $(addsuffix /*.vmem,$(TEST_DIRS))
	rm -f  $(addsuffix /*.txt,$(TEST_DIRS))
	rm -f  $(addsuffix /*.csv,$(TEST_DIRS))
	rm -f  $(addsuffix /*.log,$(TEST_DIRS))
	rm -f  $(addsuffix /*.vcd,$(TEST_DIRS))
	rm -rf $(addsuffix /obj_dir/,$(TEST_DIRS))
