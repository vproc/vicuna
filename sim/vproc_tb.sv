// // Copyright TU Wien
// // Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// // SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


// // `timescale 10us/100ns
// module vproc_tb #(
//         parameter              PROG_PATHS_LIST = "/home/hfaroo9/498-integ/ece498hk-RISCV-V-Extension/src/vicuna/sim/files.txt",
//         parameter int unsigned MEM_W           = 32,
//         parameter int unsigned MEM_SZ          = 262144,
//         parameter int unsigned MEM_LATENCY     = 1,
//         parameter int unsigned VMEM_W          = 32,
//         parameter int unsigned ICACHE_SZ       = 0,   // instruction cache size in bytes
//         parameter int unsigned ICACHE_LINE_W   = 128, // instruction cache line width in bits
//         parameter int unsigned DCACHE_SZ       = 0,   // data cache size in bytes
//         parameter int unsigned DCACHE_LINE_W   = 512  // data cache line width in bits
//     );

//     // timeunit 100ns;
//     // timeprecision 1ns; // TODO: are these correct?

//     logic clk, rst;

//     always begin
//         #1 clk = ~clk;
//     end

//     default clocking tb_clk @(negedge clk); endclocking

//     initial begin
//         clk = 0;
//     end
    
//     // Flash storage SPI
//     logic [3:0] external_qspi_io_i;
//     logic [3:0] programming_qspi_io_o;
//     logic [3:0] programming_qspi_io_t;
//     logic programming_qspi_ck_o;
//     logic programming_qspi_cs_o;

//     // Outputs
//     // From Vicuna/Ibex
//     logic vproc_mem_rvalid_i;
//     logic vproc_mem_err_i;
//     logic [32  -1:0] vproc_mem_rdata_i;
//     logic [3:0] external_qspi_io_o;
//     logic [3:0] external_qspi_io_t;
//     logic external_qspi_ck_o;
//     logic external_qspi_cs_o;
//     logic [3:0] programming_qspi_io_i;

//     // Inout
//     // To/from GPIO
//     wire [9:0] gpio_pins;

//     toplevel_498 toplevel_498(
//         .clk(clk),
//         .rst(~rst),
//         .gpio_pins(gpio_pins),

//         // To/from storage SPI
//         .external_qspi_io_i(external_qspi_io_i),
//         .external_qspi_io_o(external_qspi_io_o),
//         .external_qspi_io_t(external_qspi_io_t),
//         .external_qspi_ck_o(external_qspi_ck_o),
//         .external_qspi_cs_o(external_qspi_cs_o),

//         // To/from programming SPI
//         .programming_qspi_io_i(programming_qspi_io_i),
//         .programming_qspi_io_o(programming_qspi_io_o),
//         .programming_qspi_io_t(programming_qspi_io_t),
//         .programming_qspi_ck_o(programming_qspi_ck_o),
//         .programming_qspi_cs_o(programming_qspi_cs_o),

//         // Programming/debug set pins
//         .set_programming_mode(1'b0),
//         .set_debug_mode(1'b0) // Never used, maybe should add a debug mode
//     );

//     qspi_stub qspi_stub(
//         .qspi_io_i(external_qspi_io_i),
//         .qspi_io_o(external_qspi_io_o),
//         .qspi_io_t(external_qspi_io_t),
//         .qspi_ck_o(external_qspi_ck_o),
//         .qspi_cs_o(external_qspi_cs_o)
//     );

//     logic prog_end;
//     assign prog_end = toplevel_498.vproc_mem_req_o & (toplevel_498.vproc_top.mem_addr_o == 32'h0000_0000);
//     initial begin
//         rst = 1'b1;
//         #100
//         rst = 1'b0;

//         while (1) begin
//             @(posedge clk);
//             if(toplevel_498.vproc_mem_rvalid_i) begin
//                 $display("RVALID HIGH");
//             end
//             if(toplevel_498.vproc_mem_err_i) begin
//                 $display("ERR HIGH");
//             end
//             if(toplevel_498.vproc_mem_req_o) begin
//                 $display("vproc_mem_req_o HIGH");
//             end
//             $display("mem_req_o = %h", toplevel_498.vproc_top.mem_req_o);
//             $display("mem_addr_o = %h", toplevel_498.vproc_top.mem_addr_o);
//             $display("mem_rvalid_i = %h", toplevel_498.vproc_top.mem_rvalid_i);
//             $display("mem_err_i = %h", toplevel_498.vproc_top.mem_err_i);
//             $display("mem_rdata_i = %h", toplevel_498.vproc_top.mem_rdata_i);
//             $display("vproc_mem_we_o = %h", toplevel_498.vproc_top.mem_we_o);
//             if (prog_end) begin
//                 break;
//             end
//         end
//         $finish;
//     end

//     initial begin
//         #1000
//         $finish;
//     end

// endmodule






// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_tb #(
        parameter              PROG_PATHS_LIST = "/home/hfaroo9/498-integ/ece498hk-RISCV-V-Extension/src/vicuna/sim/files.txt",
        parameter int unsigned MEM_W           = 32,
        parameter int unsigned MEM_SZ          = 262144,
        parameter int unsigned MEM_LATENCY     = 32,
        parameter int unsigned VMEM_W          = 32,
        parameter int unsigned ICACHE_SZ       = 0,   // instruction cache size in bytes
        parameter int unsigned ICACHE_LINE_W   = 128, // instruction cache line width in bits
        parameter int unsigned DCACHE_SZ       = 0,   // data cache size in bytes
        parameter int unsigned DCACHE_LINE_W   = 512  // data cache line width in bits
    );

    logic clk, rst;
    always begin
        clk = 1'b0;
        #5;
        clk = 1'b1;
        #5;
    end

    logic        mem_req;
    logic [31:0] mem_addr;
    logic        mem_we;
    logic [3:0]  mem_be;
    logic [31:0] mem_wdata;
    logic        mem_rvalid;
    logic        mem_err;
    logic [31:0] mem_rdata;

    logic [31:0] tmp_addr;
    logic [31:0] tmp_addr2;
    // assign mem_addr = tmp_addr - 32'h0000_2000;
    logic mem_req_tmp;

    always begin
        @(posedge clk)
        if(mem_we) begin
            $display("MEM_WE HIGH");
        end
        if(mem_req_tmp) begin
            mem_addr = tmp_addr2 - 32'h0000_2000;
            tmp_addr = tmp_addr2;
            mem_req = 1'b1;
        end else begin
            mem_req = 1'b0;
        end
        // mem_req = mem_req_tmp;

    end

    // Programming/debug set pins
    logic set_programming_mode;
    logic set_debug_mode;


    logic vproc_mem_rvalid_i;
    logic vproc_mem_err_i;
    logic [MEM_W-1:0] vproc_mem_rdata_i;
    logic [31:0] vproc_pend_vreg_wr_map_o;
    logic set_valid;

    vproc_top #(
        .MEM_W         ( MEM_W                       ),
        .VMEM_W        ( VMEM_W                      ),
        .VREG_TYPE     ( vproc_pkg::VREG_GENERIC     ),
        .MUL_TYPE      ( vproc_pkg::MUL_GENERIC      ),
        .ICACHE_SZ     ( ICACHE_SZ                   ),
        .ICACHE_LINE_W ( ICACHE_LINE_W               ),
        .DCACHE_SZ     ( DCACHE_SZ                   ),
        .DCACHE_LINE_W ( DCACHE_LINE_W               )
    ) top (
        .clk_i         ( clk                         ),
        .rst_ni        ( ~rst                        ),
        .mem_req_o     ( mem_req_tmp                     ),
        .mem_addr_o    ( tmp_addr2                    ),
        .mem_we_o      ( mem_we                      ),
        .mem_be_o      ( mem_be                      ),
        .mem_wdata_o   ( mem_wdata                   ),
        .mem_rvalid_i  ( set_valid                   ),
        .mem_err_i     ( mem_err                     ),
        .mem_rdata_i   ( mem_rdata                   ),
        .pend_vreg_wr_map_o (                        )
    );
    wire [9:0] gpio_pins;

    // To/from storage SPI
    logic   [3:0]           external_qspi_io_i;
    logic   [3:0]           external_qspi_io_o;
    logic   [3:0]           external_qspi_io_t;
    logic                   external_qspi_ck_o;
    logic                   external_qspi_cs_o;

    // To/from programming SPI
    logic   [3:0]           programming_qspi_io_i;
    logic   [3:0]           programming_qspi_io_o;
    logic   [3:0]           programming_qspi_io_t;
    logic                   programming_qspi_ck_o;
    logic                   programming_qspi_cs_o;


    


    mmu #(.MEM_W(MEM_W)) mmu (
        .clk(clk),
        .rst(~rst),

        // Set mode inputs
        .set_programming_mode(set_programming_mode),
        .set_debug_mode(set_debug_mode),

        // To/from Vicuna/Ibex
        .vproc_mem_req_o(mem_req),
        .vproc_mem_addr_o(tmp_addr),
        .vproc_mem_we_o(mem_we),
        .vproc_mem_be_o(mem_be),
        .vproc_mem_wdata_o(mem_wdata),
        .vproc_mem_rvalid_i(vproc_mem_rvalid_i),
        .vproc_mem_err_i(vproc_mem_err_i),
        .vproc_mem_rdata_i(vproc_mem_rdata_i),

        // To/from GPIO
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
        .programming_qspi_cs_o(programming_qspi_cs_o)
    );

    qspi_stub qspi_stub(
        .qspi_io_i(external_qspi_io_i),
        .qspi_io_o(external_qspi_io_o),
        .qspi_io_t(external_qspi_io_t),
        .qspi_ck_o(external_qspi_ck_o),
        .qspi_cs_o(external_qspi_cs_o)
    );

    // memory
    logic [MEM_W-1:0]                    mem[MEM_SZ/(MEM_W/8)];
    logic [$clog2(MEM_SZ/(MEM_W/8))-1:0] mem_idx;
    assign mem_idx = mem_addr[$clog2(MEM_SZ)-1 : $clog2(MEM_W/8)];
    // latency pipeline
    logic        mem_rvalid_queue[MEM_LATENCY];
    logic [31:0] mem_rdata_queue [MEM_LATENCY];
    logic        mem_err_queue   [MEM_LATENCY];
    always begin
	#5;
        if (mem_req & mem_we) begin
            for (int i = 0; i < MEM_W/8; i++) begin
                if (mem_be[i]) begin
                    mem[mem_idx][i*8 +: 8] <= mem_wdata[i*8 +: 8];
                end
            end
        end
        for (int i = 1; i < MEM_LATENCY; i++) begin
            if (i == 1) begin
                mem_rvalid_queue[i] <= mem_req;
                mem_rdata_queue [i] <= mem[mem_idx];
                mem_err_queue   [i] <= mem_addr[31:$clog2(MEM_SZ)] != '0;
            end else begin
                mem_rvalid_queue[i] <= mem_rvalid_queue[i-1];
                mem_rdata_queue [i] <= mem_rdata_queue [i-1];
                mem_err_queue   [i] <= mem_err_queue   [i-1];
            end
        end
        if ((MEM_LATENCY) == 1)begin
            mem_rvalid <= mem_req;
            mem_rdata  <= mem[mem_idx];
            mem_err    <= mem_addr[31:$clog2(MEM_SZ)] != '0;
        end else begin
            mem_rvalid <= mem_rvalid_queue[MEM_LATENCY-1];
            mem_rdata  <= mem_rdata_queue [MEM_LATENCY-1];
            mem_err    <= mem_err_queue   [MEM_LATENCY-1];
        end
//        for (int i = 0; i < MEM_SZ; i++) begin
            // set the don't care values in the memory to 0 during the first rising edge
//            if ($isunknown(mem[i]) & ($time < 10)) begin
//                mem[i] <= '0;
//            end
//        end
	#5;
    end

    logic prog_end, done;
    assign prog_end = mem_req & (mem_addr == '0);

    integer fd1, fd2, cnt, ref_start, ref_end, dump_start, dump_end;
    string  line, prog_path, ref_path, dump_path;

    logic mmu_valid;
    logic mem_valid;
    logic [31:0] mmu_val;
    logic [31:0] mem_val;
    logic [31:0] prev_addr;
    initial begin
	$display("STARTING TB");
        done = 1'b0;
        mmu_valid = 1'b0;
        mem_valid = 1'b0;
        prev_addr = 32'b0;
        set_valid = 1'b0;

        fd1 = $fopen(PROG_PATHS_LIST, "r");
        for (int i = 0; !$feof(fd1); i++) begin
            rst = 1'b1;

            $fgets(line, fd1);

            ref_path   = "/dev/null";
            ref_start  = 0;
            ref_end    = 0;
            dump_path  = "/dev/null";
            dump_start = 0;
            dump_end   = 0;
            cnt = $sscanf(line, "%s %s %x %x %s %x %x", prog_path, ref_path, ref_start, ref_end, dump_path, dump_start, dump_end);

            // continue with next line in case of an empty line (cnt == 0) or an EOF (cnt == -1)
            if (cnt < 1) begin
                continue;
            end

            $display("ABOUT TO READ MEM (%s)", prog_path);
            $readmemh(prog_path, mem);
            $display("FINISHED READ MEM");

	    for(int j = 0; j < MEM_SZ; j++) begin
		if($isunknown(mem[j])) begin
		    mem[j] = 0;
		end
	    end

            fd2 = $fopen(ref_path, "w");
	    $display("REF PATH OPEN (%s)", ref_path);
            for (int j = ref_start / (MEM_W/8); j < ref_end / (MEM_W/8); j++) begin
                for (int k = 0; k < MEM_W/32; k++) begin
		    if($isunknown(mem[j][k*32 +: 32])) begin
		        mem[j][k*32 +: 32] = 0;
		    end
 
		    // $display("%x", mem[j][k*32 +: 32]);
                    $fwrite(fd2, "%x\n", mem[j][k*32 +: 32]);
                end
            end
            $fclose(fd2);
	    $display("REF PATH CLOSED");

            // reset for 100 cycles
            #100
            rst = 1'b0;

            // wait for completion (i.e. request of instr mem addr 0x00000000)
            //@(posedge prog_end);
	    $display("STARTING WHILE LOOP");
            while (1) begin
                @(posedge clk);
                if(tmp_addr != prev_addr) begin
                    $display("new addr (prev = %x, new = %x)", prev_addr, tmp_addr);
                    prev_addr = tmp_addr;
                end

                if (mmu_valid == 1'b0 && vproc_mem_rvalid_i == 1'b1) begin
                    mmu_valid = 1'b1;
                    mmu_val = vproc_mem_rdata_i;
                    // $display("mmu valid at t=%x", $time);
                    $display("mmu valid at t=%x (tmp_addr = %x, vproc_mem_rdata_i = %x, mmu_val = %x)", $time, tmp_addr, vproc_mem_rdata_i, mmu_val);
                end

                if(mem_valid == 1'b0 && mem_rvalid == 1'b1) begin
                    mem_valid = 1'b1;
                    mem_val = mem_rdata;
                    $display("mem valid at t=%x (addr = %x, idx = %x, mem_rdata = %x, mem_val = %x)", $time, mem_addr, mem_idx, mem_rdata, mem_val);
                end

                if (set_valid) begin
                    set_valid = 1'b0;
                end

                if(mem_valid == 1'b1 && mmu_valid == 1'b1) begin
                    mem_valid = 1'b0;
                    mmu_valid = 1'b0;
                    set_valid = 1'b1;
                    $display("Both valid");
                    assert (mmu_val == mem_val) else begin
                        $error("ERROR: mmu_val = %x, mem_val = %x, tmp_addr = %x, mem_addr = %x, mem_idx = %x, vproc_mem_rdata_i = %x, mem_rdata = %x, mem[mem_idx] = %x", mmu_val, mem_val, tmp_addr, mem_addr, mem_idx, vproc_mem_rdata_i, mem_rdata, mem[mem_idx]);
                        $finish;
                    end
                end
            end
            if (prog_end) begin
                break;
            end
	    $display("OUT OF WHILE LOOP");

            fd2 = $fopen(dump_path, "w");
            for (int j = dump_start / (MEM_W/8); j < dump_end / (MEM_W/8); j++) begin
                for (int k = 0; k < MEM_W/32; k++) begin
                    $fwrite(fd2, "%x\n", mem[j][k*32 +: 32]);
                end
            end
            $fclose(fd2);
        end
        $fclose(fd1);
        done = 1'b1;
	$finish;
    end

endmodule
