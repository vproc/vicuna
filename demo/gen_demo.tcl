# Copyright TU Wien
# Licensed under the ISC license, see LICENSE.txt for details
# SPDX-License-Identifier: ISC


################################################################################
# Create Project
################################################################################

if {$argc != 7} {
    puts "usage: gen_demo.tcl VPROC-DIR CORE-DIR PART CONSTR-FILE RAM-FILE DIFF-CLK CLK-PER"
    exit 2
}

# get command line arguments:
set vproc_dir    [lindex $argv 0]
set core_dir     [lindex $argv 1]
set part         [lindex $argv 2]
set constr_file  [lindex $argv 3]
set ram_file_var "RAM_FPATH=\"[lindex $argv 4]\""
set diff_clk_var "DIFF_CLK=[lindex $argv 5]"
set clk_per_var  "SYSCLK_PER=[lindex $argv 6]"

# create project:
set _xil_proj_name_ "vicuna_demo"
create_project -part $part ${_xil_proj_name_} ${_xil_proj_name_}
set proj_dir [get_property directory [current_project]]

# set project properties
set obj [current_project]
set_property -name "default_lib" -value "xil_defaultlib" -objects $obj
set_property -name "dsa.accelerator_binary_content" -value "bitstream" -objects $obj
set_property -name "dsa.accelerator_binary_format" -value "xclbin2" -objects $obj
set_property -name "dsa.description" -value "Vivado generated DSA" -objects $obj
set_property -name "dsa.dr_bd_base_address" -value "0" -objects $obj
set_property -name "dsa.emu_dir" -value "emu" -objects $obj
set_property -name "dsa.flash_interface_type" -value "bpix16" -objects $obj
set_property -name "dsa.flash_offset_address" -value "0" -objects $obj
set_property -name "dsa.flash_size" -value "1024" -objects $obj
set_property -name "dsa.host_architecture" -value "x86_64" -objects $obj
set_property -name "dsa.host_interface" -value "pcie" -objects $obj
set_property -name "dsa.platform_state" -value "pre_synth" -objects $obj
set_property -name "dsa.uses_pr" -value "1" -objects $obj
set_property -name "dsa.vendor" -value "xilinx" -objects $obj
set_property -name "dsa.version" -value "0.0" -objects $obj
set_property -name "enable_vhdl_2008" -value "1" -objects $obj
set_property -name "ip_cache_permissions" -value "read write" -objects $obj
set_property -name "ip_output_repo" -value "$proj_dir/${_xil_proj_name_}.cache/ip" -objects $obj
set_property -name "mem.enable_memory_map_generation" -value "1" -objects $obj
set_property -name "part" -value $part -objects $obj
set_property -name "sim.central_dir" -value "$proj_dir/${_xil_proj_name_}.ip_user_files" -objects $obj
set_property -name "sim.ip.auto_export_scripts" -value "1" -objects $obj
set_property -name "simulator_language" -value "Mixed" -objects $obj

# add source files:
set obj [get_filesets sources_1]
set src_list {}
lappend src_list "$vproc_dir/demo/rtl/demo_top.sv"
lappend src_list "$vproc_dir/demo/rtl/ram.sv"
lappend src_list "$vproc_dir/demo/rtl/uart_rx.sv"
lappend src_list "$vproc_dir/demo/rtl/uart_tx.sv"
foreach file {
    vproc_top.sv vproc_pkg.sv vproc_core.sv vproc_decoder.sv vproc_lsu.sv vproc_alu.sv
    vproc_mul.sv vproc_mul_block.sv vproc_sld.sv vproc_elem.sv vproc_hazards.sv vproc_vregfile.sv
    vproc_vregpack.sv vproc_vregunpack.sv vproc_queue.sv
} {
    lappend src_list "$vproc_dir/rtl/$file"
}
# identify the main core form the core directory pathname
set main_core ""
if {[string first "ibex" $core_dir] != -1} {
    set main_core "ibex"
    foreach file {ibex_pkg.sv ibex_top.sv ibex_core.sv ibex_alu.sv ibex_branch_predict.sv
                  ibex_compressed_decoder.sv ibex_controller.sv ibex_counter.sv
                  ibex_cs_registers.sv ibex_csr.sv ibex_decoder.sv ibex_dummy_instr.sv
                  ibex_ex_block.sv ibex_fetch_fifo.sv ibex_icache.sv ibex_id_stage.sv
                  ibex_if_stage.sv ibex_load_store_unit.sv ibex_lockstep.sv
                  ibex_multdiv_fast.sv ibex_multdiv_slow.sv ibex_pmp.sv ibex_prefetch_buffer.sv
                  ibex_register_file_ff.sv ibex_register_file_fpga.sv ibex_wb_stage.sv
                  ibex_tracer_pkg.sv ibex_tracer.sv} {
        lappend src_list "$core_dir/rtl/$file"
    }
    lappend src_list "$core_dir/syn/rtl/prim_clock_gating.v"
    lappend src_list "$core_dir/vendor/lowrisc_ip/dv/sv/dv_utils/"
    lappend src_list "$core_dir/vendor/lowrisc_ip/ip/prim/rtl/"
}
add_files -fileset $obj -norecurse -scan_for_includes $src_list

# add simulation only files:
set obj [get_filesets sim_1]
set src_list {}
lappend src_list "$vproc_dir/demo/rtl/demo_tb.sv"
add_files -fileset $obj -norecurse -scan_for_includes $src_list

# set top modules:
set_property top demo_top [get_filesets sources_1]
set_property top demo_tb [get_filesets sim_1]
set_property top_lib xil_defaultlib [get_filesets sim_1]

# add constraint files:
set obj [get_filesets constrs_1]
add_files -fileset $obj -norecurse $constr_file

# set memory initialization files:
set_property generic "$ram_file_var $diff_clk_var $clk_per_var" -objects [get_filesets sources_1]
set_property generic "$ram_file_var $diff_clk_var $clk_per_var" -objects [get_filesets sim_1]
