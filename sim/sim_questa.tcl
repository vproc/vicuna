# Copyright CSEM
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


if {$argc < 6} {
    puts "usage: sim.tcl VPROC_DIR CORE_DIR CONFIG_FILE PARAMS LOG_FILE PROG_PATHS_LIST \[SYMBOLS ...\]"
    exit 2
}

# get command line arguments
set vproc_dir $1
set core_dir $2
set config_file_path $3
set params_var $4
set log_file_path $5
set prog_paths_var $6
set log_signals $7

# default values for dv_utils and prim
set dv_utils ""
set prim ""

lassign $params_var VMEM_W MEM_W MEM_SZ MEM_LATENCY ICACHE_SZ ICACHE_LINE_W DCACHE_SZ DCACHE_LINE_W

# RAM_TYPE=2 is translated to vproc_pkg::RAM_ASIC
set RAM_TYPE "2"
# MUL_TYPE=0 is translated to vproc_pkg::MUL_GENERIC
set MUL_TYPE "0"

# create source file list
lappend src_list "$vproc_dir/rtl/vproc_pkg.sv"
lappend src_list "$config_file_path"
lappend src_list "$vproc_dir/sim/vproc_tb.sv"
set main_core ""
if {[string first "ibex" $core_dir] != -1} {
    set main_core "MAIN_CORE_IBEX"
    lappend src_list "$core_dir/rtl/ibex_pkg.sv"
    lappend src_list "$core_dir/rtl/ibex_tracer_pkg.sv"
    lappend src_list "$core_dir/vendor/lowrisc_ip/ip/prim/rtl/prim_ram_1p_pkg.sv"
    foreach file [glob -type f $core_dir\/*rtl\/*\[a-z,_\]*.sv] {
        lappend src_list $file
    }
    lappend src_list "$core_dir/syn/rtl/prim_clock_gating.v"
    set dv_utils "$core_dir/vendor/lowrisc_ip/dv/sv/dv_utils/"
    set prim "$core_dir/vendor/lowrisc_ip/ip/prim/rtl/"
} elseif {[string first "cv32e40x" $core_dir] != -1} {
    set main_core "MAIN_CORE_CV32E40X"
    lappend src_list "$core_dir/rtl/include/cv32e40x_pkg.sv"
    foreach file [glob -type f $core_dir\/*rtl\/*\[a-z,_\]*.sv] {
        lappend src_list $file
    }
    lappend src_list "$core_dir/bhv/cv32e40x_sim_clock_gate.sv"
}
foreach file [glob -type f $vproc_dir\/*rtl\/*\[a-z,_\]*.sv] {
    lappend src_list $file
}

vlib work

foreach file $src_list {vlog -work work $file +define+$main_core +incdir+$prim+$dv_utils}

vopt +acc vproc_tb -o vproc_tb_opt -debugdb -G VMEM_W=$VMEM_W      \
     -G MEM_W=$MEM_W -G MEM_SZ=$MEM_SZ -G MEM_LATENCY=$MEM_LATENCY \
     -G ICACHE_SZ=$ICACHE_SZ -G ICACHE_LINE_W=$ICACHE_LINE_W       \
     -G DCACHE_SZ=$DCACHE_SZ -G DCACHE_LINE_W=$DCACHE_LINE_W       \
     -G RAM_TYPE=$RAM_TYPE -G MUl_TYPE=$MUL_TYPE                   \
     +define+$main_core -G PROG_PATHS_LIST=$prog_paths_var

vsim -work work vproc_tb_opt

# add trace_signals
foreach sig $log_signals {
    add wave $sig
}

set complete_signal "done"
add wave "done"

set outf [open $log_file_path "w"]
puts "logging following signals to $log_file_path: $log_signals"

foreach sig $log_signals {
    set sig_name_start [string wordstart $sig end]
    puts -nonewline $outf "[string range $sig $sig_name_start end];"
}
puts $outf ""

for {set step 0} 1 {incr step} {
    # log the value of each signal
    foreach sig $log_signals {
        puts -nonewline $outf "[examine -noshowbase $sig];"
    }
    puts $outf ""
    # advance by 1 clock cycle
    run 10 ns

    # check if the abort condition has been met
    if {[examine -noshowbase $complete_signal] == "1"} {
        puts "exit condition met after $step clock cycles"
        break
    }
}

exit -f
