// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


// `timescale 10us/100ns
module vproc_tb #(
        parameter              PROG_PATHS_LIST = "/home/hfaroo9/ece498hk-RISCV-V-Extension/src/vicuna/sim/files.txt",
        parameter int unsigned MEM_W           = 32,
        parameter int unsigned MEM_SZ          = 262144,
        parameter int unsigned MEM_LATENCY     = 1,
        parameter int unsigned VMEM_W          = 32,
        parameter int unsigned ICACHE_SZ       = 0,   // instruction cache size in bytes
        parameter int unsigned ICACHE_LINE_W   = 128, // instruction cache line width in bits
        parameter int unsigned DCACHE_SZ       = 0,   // data cache size in bytes
        parameter int unsigned DCACHE_LINE_W   = 512  // data cache line width in bits
    );

    // timeunit 100ns;
    // timeprecision 1ns; // TODO: are these correct?

    logic clk, rst;

    always begin
        #1 clk = ~clk;
    end

    default clocking tb_clk @(negedge clk); endclocking

    initial begin
        clk = 0;
    end
    
    // Flash storage SPI
    logic [3:0] external_qspi_io_i;
    logic [3:0] programming_qspi_io_o;
    logic [3:0] programming_qspi_io_t;
    logic programming_qspi_ck_o;
    logic programming_qspi_cs_o;

    // Outputs
    // From Vicuna/Ibex
    logic vproc_mem_rvalid_i;
    logic vproc_mem_err_i;
    logic [32  -1:0] vproc_mem_rdata_i;
    logic [3:0] external_qspi_io_o;
    logic [3:0] external_qspi_io_t;
    logic external_qspi_ck_o;
    logic external_qspi_cs_o;
    logic [3:0] programming_qspi_io_i;

    // Inout
    // To/from GPIO
    wire [9:0] gpio_pins;

    toplevel_498 toplevel_498(
        .clk(clk),
        .rst(~rst),
        .gpio_pins(gpio_pins),

        // To/from storage SPI
        .external_qspi_io_i(external_qspi_io_i),
        .external_qspi_io_o(external_qspi_io_o),
        .external_qspi_io_t(external_qspi_io_t),
        .external_qspi_ck_o(external_qspi_ck_o),
        .external_qspi_cs_o(external_qspi_cs_o),

        // To/from programming SPI
        .programming_qspi_io_i(programming_qspi_io_i),
        .programming_qspi_io_o(programming_qspi_io_o),
        .programming_qspi_io_t(programming_qspi_io_t),
        .programming_qspi_ck_o(programming_qspi_ck_o),
        .programming_qspi_cs_o(programming_qspi_cs_o),

        // Programming/debug set pins
        .set_programming_mode(1'b0),
        .set_debug_mode(1'b0) // Never used, maybe should add a debug mode
    );

    qspi_stub qspi_stub(
        .qspi_io_i(external_qspi_io_i),
        .qspi_io_o(external_qspi_io_o),
        .qspi_io_t(external_qspi_io_t),
        .qspi_ck_o(external_qspi_ck_o),
        .qspi_cs_o(external_qspi_cs_o)
    );

    logic prog_end;
    assign prog_end = ~toplevel_498.vproc_mem_req_o & (toplevel_498.vproc_top.mem_addr_o == 32'h0000_2000);
    initial begin
        rst = 1'b1;
        #100
        rst = 1'b0;

        while (1) begin
            @(posedge clk);
            if(toplevel_498.vproc_mem_rvalid_i) begin
                $display("RVALID HIGH");
            end
            if(toplevel_498.vproc_mem_err_i) begin
                $display("ERR HIGH");
            end
            if(toplevel_498.vproc_mem_req_o) begin
                $display("vproc_mem_req_o HIGH");
            end
            $display("mem_req_o = %h", toplevel_498.vproc_top.mem_req_o);
            $display("mem_addr_o = %h", toplevel_498.vproc_top.mem_addr_o);
            // $display("mem_rvalid_i = %h", toplevel_498.vproc_top.mem_rvalid_i);
            // $display("mem_err_i = %h", toplevel_498.vproc_top.mem_err_i);
            // $display("mem_rdata_i = %h", toplevel_498.vproc_top.mem_rdata_i);
            if (prog_end) begin
                break;
            end
        end
        $finish;
    end

endmodule
