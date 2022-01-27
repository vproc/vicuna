# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


################################################################################
# TCL script for use with the Vivado FPGA synthesis tool. Does a binary search
# to find the maximum frequency at which an FPGA design can run.

if {$argc < 4 || $argc > 5} {
    puts "usage: get_max_clk.tcl PROJECT START_FREQ STEP_SZ REF_CLK \[PART\]"
    puts "    PROJECT    : Full path name of the Vivado project (*.xpr) file"
    puts "    START_FREQ : Initial clock frequency in MHz"
    puts "    STEP_SZ    : Initial step size in MHz (gets halved every round)"
    puts "    CLK_NAME   : PLL input clock name (used in create_clock command)"
    puts "    PART       : Optionally specify an alternate part to be used"
    exit 1
}

# get command line arguments
set proj_path  [lindex $argv 0]
set start_freq [lindex $argv 1]
set step_sz    [lindex $argv 2]
set clk_name   [lindex $argv 3]

# valid PLL VCO range in ns (800 MHz - 1600 MHz => 0.625 ns - 1.25 ns)
set pll_vco_min 0.625
set pll_vco_max 1.25

# open project
if {$argc != 5} {
    open_project $proj_path
} else {
    open_project -part [lindex $argv 4] $proj_path
}

# get the period of the PLL input clock, i.e., the reference clock period
update_compile_order -fileset sources_1
synth_design -rtl
set ref_clk [get_property PERIOD [get_clocks $clk_name]]

# open output log file
set outf [open get_max_clk.log w]
puts $outf [format "Reference clock: $clk_name, period: %.3f ns" $ref_clk]

# identify valid PLL multiplier settings for the given reference clock period
set pll_mul_vals {}
for {set val 1} 1 {incr val} {
    set vco_per [expr $ref_clk / double($val)]
    if {$vco_per < $pll_vco_min} {
        break
    } elseif {$vco_per <= $pll_vco_max} {
        lappend pll_mul_vals $val
    }
}

# last frequency to pass the timing analysis
set pass_freq 0.

for {set step 0} 1 {incr step} {
    puts $outf [format "  Seeking PLL settings for %.2f MHz clock" $start_freq]

    # target clock period in ns
    set clk_per [expr 1000. / $start_freq]

    # initial PLL multiplier and divisor values
    set pll_mul 1
    set pll_div 1
    set best_diff 1.

    # iterate through all possible multiplier values and nearby divisor values
    # and find closest matching pair
    foreach mul $pll_mul_vals {
        set div [expr round(($clk_per * $mul) / $ref_clk) - 2]

        for {set i 0} {$i < 5} {incr i} {
            set per [expr (double($ref_clk) * $div) / $mul]
            set diff [expr abs(1. - $clk_per / $per)]

            if {$diff < $best_diff} {
                set pll_mul $mul
                set pll_div $div
                set best_diff $diff
            }
            incr div
        }
    }

    set clk_freq [expr (1000. / $ref_clk) * $pll_mul / $pll_div]

    puts $outf [format "  Closest PLL setting: mul $pll_mul, div $pll_div => clk freq %.2f MHz (deviates by %.2f %%)" $clk_freq [expr $best_diff * 100.]]
    flush $outf

    # set PLL multiplier and divider
    set pll_mul_var "PLL_MUL=$pll_mul"
    set pll_div_var "PLL_DIV=$pll_div"
    set_property generic "$pll_mul_var $pll_div_var" -objects [get_filesets sources_1]

    # run synthesize and implementation
    reset_runs {synth_1 impl_1}
    launch_runs synth_1 -quiet; list
    wait_on_run synth_1; list
    launch_runs impl_1 -to_step route_design -quiet; list
    wait_on_run impl_1; list

    # get worst-case slack (which indicates whether timing passes)
    open_run impl_1
    set wc_slack [get_property SLACK [get_timing_paths]]

    if {$wc_slack >= 0.} {
        # timing passed, increase clock frequency
        set pass_freq $clk_freq
        puts $outf [format "\[PASS\] %.2f MHz (WNS: %.3f)" $clk_freq $wc_slack]
        set start_freq [expr $start_freq + $step_sz]

        # while we are here, print the resource utilization of that design
        report_utilization -hierarchical -file utilization_report.rpt
    } else {
        # timing failed, decrease clock frequency
        puts $outf [format "\[FAIL\] %.2f MHz (WNS: %.3f)" $clk_freq $wc_slack]
        set start_freq [expr $start_freq - $step_sz]
    }
    flush $outf

    close_design

    if {$step_sz <= 0.5} {
        puts $outf "Step size too small, exiting ..."
        break
    }
    set step_sz [expr $step_sz / 2.0]
}

puts $outf [format "Max. frequency: %.2f MHz" $pass_freq]
close $outf
