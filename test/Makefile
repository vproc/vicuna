# Copyright TU Wien
# Licensed under the ISC license, see LICENSE.txt for details
# SPDX-License-Identifier: ISC


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

# test directories
TEST_DIRS := lsu alu mul sld elem csr kernel

# test targets
TESTS_ALL := $(TEST_DIRS) $(addsuffix /, $(TEST_DIRS))
TESTS_ALL := $(TESTS_ALL) $(basename $(shell find $(TEST_DIRS) -name '*.S'))


.PHONY: all $(TESTS_ALL)
all: $(TESTS_ALL)


# TODO find ways to check that:
# - all parameters are initialized
lint: lint-verible lint-verilator

# Verible Linting Rules
# change rule parameters
LINT_VERIBLE := typedef-structs-unions=allow_anonymous_nested:true
LINT_VERIBLE := $(LINT_VERIBLE),parameter-name-style=localparam_style:ALL_CAPS
LINT_VERIBLE := $(LINT_VERIBLE),line-length=length:200
# enable rules
LINT_VERIBLE := $(LINT_VERIBLE),port-name-suffix,proper-parameter-declaration
LINT_VERIBLE := $(LINT_VERIBLE),signal-name-style
# disable rules
LINT_VERIBLE := $(LINT_VERIBLE),-generate-label,-struct-union-name-style
LINT_VERIBLE := $(LINT_VERIBLE),-explicit-parameter-storage-type
LINT_VERIBLE := $(LINT_VERIBLE),-undersized-binary-literal
lint-verible:
	verible-verilog-lint --rules="$(LINT_VERIBLE)"                            \
	    `ls $(TEST_DIR)/../rtl/*.sv | grep -v vproc_pkg.sv`

lint-verilator:
	verilator -Wall -Wno-PINCONNECTEMPTY -Wno-UNUSED -Wno-UNDRIVEN            \
		-Wno-UNSIGNED -Wno-DECLFILENAME                                       \
	    -I$(TEST_DIR)/../rtl/ --cc vproc_pkg.sv vproc_core.sv                 \
	    vproc_hazards.sv vproc_vregpack.sv vproc_vregunpack.sv                \
	    --top-module vproc_core --clk clk_i --lint-only


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
	    echo "[CONFIG ] $@ $$line";                                           \
	    make -f $(TEST_DIR)/../sim/Makefile $(SIMULATOR) $$line               \
	        PROG_PATHS_LIST=progs.txt CORE_DIR=$(CORE_DIR) ENABLE_SVA=1       \
	        TRACE_SIGS="`cat $(TEST_DIR)/trace-sigs.conf`" >sim.log 2>&1;     \
	    if [ "$$?" != "0" ]; then                                             \
	        echo "[ ERROR ] $@ simulation failed; content of $@/sim.log:";    \
	        cat sim.log;                                                      \
	        exit 1;                                                           \
	    fi;                                                                   \
	    wr_hazard_col=`head -n 1 sim_trace.csv | sed 's/;/\n/g' |             \
	                   grep -n vreg_wr_hazard_map_q |                         \
	                   awk -F ':' '{print $$1}'`;                             \
	    if [[ "$$wr_hazard_col" =~ ^[0-9]+$$ ]]; then                         \
	        hazards=`tail -n 1 sim_trace.csv |                                \
	                 awk -F ';' -v idx="$$wr_hazard_col" '{print $$idx}'`;    \
	        if [ "$$hazards" != "00000000" ]; then                            \
	            echo "[WARNING] $@ uncleared write hazard(s) (0x$${hazards})";\
	        fi;                                                               \
	    else                                                                  \
	        echo "[WARNING] $@ write hazards are not among traced signals";   \
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
	            printf '[ ERROR ] %-30s %s\n' $@/$$prog_name "$$perf_info";   \
	            echo "incorrect memory content; diff:";                       \
	            echo "$$memdiff";                                             \
	            retval=1;                                                     \
	        else                                                              \
	            printf '[SUCCESS] %-30s %s\n' $@/$$prog_name "$$perf_info";   \
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
	make -f $(TEST_DIR)/../sw/Makefile PROG=$$prog OBJ="$$obj" >$$log 2>&1;   \
	if [ "$$?" != "0" ]; then                                                 \
	    echo "[ ERROR ] $@ build failed; content of $$log:";                  \
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
