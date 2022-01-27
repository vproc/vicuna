// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_cache #(
        parameter int unsigned ADDR_BIT_W  = 16, // Address width (bits)
        parameter int unsigned CPU_BYTE_W  = 4,  // CPU data width (bytes)
        parameter int unsigned MEM_BYTE_W  = 4,  // Memory data width (bytes)
        parameter int unsigned LINE_BYTE_W = 16, // Cache line width (bytes)
        parameter int unsigned WAY_LEN     = 256 // Cache way length (lines)
    )
    (
        input  logic                    clk_i,
        input  logic                    rst_ni,

        input  logic                    hold_mem_i,

        // CPU request interface
        input  logic                    cpu_req_i,
        input  logic [ADDR_BIT_W-1:0]   cpu_addr_i,
        input  logic                    cpu_we_i,
        input  logic [CPU_BYTE_W-1:0]   cpu_be_i,
        input  logic [CPU_BYTE_W*8-1:0] cpu_wdata_i,
        output logic                    cpu_gnt_o,
        output logic                    cpu_rvalid_o,
        output logic [CPU_BYTE_W*8-1:0] cpu_rdata_o,
        output logic                    cpu_err_o,

        // Memory request interface
        output logic                    mem_req_o,
        output logic [ADDR_BIT_W-1:0]   mem_addr_o,
        output logic                    mem_we_o,
        output logic [MEM_BYTE_W*8-1:0] mem_wdata_o,
        input  logic                    mem_gnt_i,
        input  logic                    mem_rvalid_i,
        input  logic [MEM_BYTE_W*8-1:0] mem_rdata_i,
        input  logic                    mem_err_i
    );

    // number of memory requests required to fill or spill a cache line:
    localparam int unsigned LINE_FILL_REQ_CNT = LINE_BYTE_W / MEM_BYTE_W;

    typedef union packed {
        logic [$clog2(LINE_FILL_REQ_CNT):0] val; // intentionally one bit more
        struct packed {
            logic                                 done;
            logic [$clog2(LINE_FILL_REQ_CNT)-1:0] cnt;
        } part;
    } mem_counter_t;

    //
    localparam int unsigned TAG_BIT_W    = ADDR_BIT_W - $clog2(WAY_LEN * LINE_BYTE_W);
    localparam int unsigned INDEX_BIT_W  = $clog2(WAY_LEN);
    localparam int unsigned OFFSET_BIT_W = $clog2(LINE_BYTE_W);

    typedef union packed {
        logic [ADDR_BIT_W-1:0] addr;
        struct packed {
            logic [TAG_BIT_W-1:0]    tag;    // line tag part
            logic [INDEX_BIT_W-1:0]  index;  // line index part
            logic [OFFSET_BIT_W-1:0] offset; // byte offset part
        } part;
    } cpu_addr_t;


    // cache ways:
    logic [INDEX_BIT_W-1:0]   way_windex;
    logic                     way0_we;
    logic                     way1_we;
    logic [TAG_BIT_W-1:0]     way_wtag;
    logic [LINE_BYTE_W-1:0]   way_wline_be;
    logic [LINE_BYTE_W*8-1:0] way_wline_data;
    logic                     way_wdirty;
    logic                     way_werr;
    logic [INDEX_BIT_W-1:0]   way_rindex;
    logic [TAG_BIT_W-1:0]     way0_rtag;
    logic [LINE_BYTE_W*8-1:0] way0_rline;
    logic                     way0_rdirty;
    logic                     way0_rerr;
    logic [TAG_BIT_W-1:0]     way1_rtag;
    logic [LINE_BYTE_W*8-1:0] way1_rline;
    logic                     way1_rdirty;
    logic                     way1_rerr;

    vproc_cache_way #(
        .TAG_BIT_W    ( TAG_BIT_W      ),
        .INDEX_BIT_W  ( INDEX_BIT_W    ),
        .LINE_BYTE_W  ( LINE_BYTE_W    )
    ) way0 (
        .clk_i        ( clk_i          ),
        .windex_i     ( way_windex     ),
        .we_i         ( way0_we        ),
        .wtag_i       ( way_wtag       ),
        .wline_be_i   ( way_wline_be   ),
        .wline_data_i ( way_wline_data ),
        .wdirty_i     ( way_wdirty     ),
        .werr_i       ( way_werr       ),
        .rindex_i     ( way_rindex     ),
        .rtag_o       ( way0_rtag      ),
        .rline_o      ( way0_rline     ),
        .rdirty_o     ( way0_rdirty    ),
        .rerr_o       ( way0_rerr      )
    );

    vproc_cache_way #(
        .TAG_BIT_W    ( TAG_BIT_W      ),
        .INDEX_BIT_W  ( INDEX_BIT_W    ),
        .LINE_BYTE_W  ( LINE_BYTE_W    )
    ) way1 (
        .clk_i        ( clk_i          ),
        .windex_i     ( way_windex     ),
        .we_i         ( way1_we        ),
        .wtag_i       ( way_wtag       ),
        .wline_be_i   ( way_wline_be   ),
        .wline_data_i ( way_wline_data ),
        .wdirty_i     ( way_wdirty     ),
        .werr_i       ( way_werr       ),
        .rindex_i     ( way_rindex     ),
        .rtag_o       ( way1_rtag      ),
        .rline_o      ( way1_rline     ),
        .rdirty_o     ( way1_rdirty    ),
        .rerr_o       ( way1_rerr      )
    );


    // cache state:
    logic                    check_tag_q,    check_tag_d;
    logic [WAY_LEN-1:0]      lru_q,          lru_d;          // LRU bits
    logic [WAY_LEN-1:0]      way0_valid_q,   way0_valid_d;   // way 0 valid bits
    logic [WAY_LEN-1:0]      way1_valid_q,   way1_valid_d;   // way 1 valid bits
    cpu_addr_t               cpu_addr_q,     cpu_addr_d;     // CPU address buffer
    logic                    cpu_we_q,       cpu_we_d;       // CPU write request
    logic [CPU_BYTE_W-1:0]   cpu_wbe_q,      cpu_wbe_d;      // CPU write byte enable
    logic [CPU_BYTE_W*8-1:0] cpu_wdata_q,    cpu_wdata_d;    // CPU write data
    mem_counter_t            mem_req_cnt_q,  mem_req_cnt_d;  // memory request counter
    mem_counter_t            mem_data_cnt_q, mem_data_cnt_d; // memory data counter

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            check_tag_q              <= '0;
            lru_q                    <= '0;
            way0_valid_q             <= '0;
            way1_valid_q             <= '0;
            cpu_addr_q.addr          <= '0;
            cpu_we_q                 <= '0;
            cpu_wbe_q                <= '0;
            cpu_wdata_q              <= '0;
            mem_req_cnt_q.part.done  <= 1'b1;
            mem_req_cnt_q.part.cnt   <= '0;
            mem_data_cnt_q.part.done <= 1'b1;
            mem_data_cnt_q.part.cnt  <= '0;
        end else begin
            check_tag_q    <= check_tag_d;
            lru_q          <= lru_d;
            way0_valid_q   <= way0_valid_d;
            way1_valid_q   <= way1_valid_d;
            cpu_addr_q     <= cpu_addr_d;
            cpu_we_q       <= cpu_we_d;
            cpu_wbe_q      <= cpu_wbe_d;
            cpu_wdata_q    <= cpu_wdata_d;
            mem_req_cnt_q  <= mem_req_cnt_d;
            mem_data_cnt_q <= mem_data_cnt_d;
        end
    end

    logic                     tag_match_way0, tag_match_way1;
    logic [LINE_BYTE_W*8-1:0] tag_match_line;
    logic                     tag_match_err;
    assign tag_match_way0 = way0_valid_q[cpu_addr_q.part.index] & (way0_rtag == cpu_addr_q.part.tag);
    assign tag_match_way1 = way1_valid_q[cpu_addr_q.part.index] & (way1_rtag == cpu_addr_q.part.tag);
    assign tag_match_line = tag_match_way0 ? way0_rline : way1_rline;
    assign tag_match_err  = tag_match_way0 ? way0_rerr  : way1_rerr;

    logic                     cache_hit, cache_miss, cache_spill;
    logic [TAG_BIT_W-1:0]     spill_tag;
    logic [LINE_BYTE_W*8-1:0] spill_line;
    assign cache_hit   = check_tag_q & (tag_match_way0 | tag_match_way1);
    assign cache_miss  = check_tag_q & ~tag_match_way0 & ~tag_match_way1;
    assign cache_spill = cache_miss & (lru_q[cpu_addr_q.part.index] ? way1_rdirty : way0_rdirty);
    assign spill_tag   = lru_q[cpu_addr_q.part.index] ? way1_rtag   : way0_rtag;
    assign spill_line  = lru_q[cpu_addr_q.part.index] ? way1_rline  : way0_rline;

    logic [OFFSET_BIT_W-1:0] cpu_addr_offset;
    generate
        if (LINE_BYTE_W > CPU_BYTE_W) begin
            assign cpu_addr_offset = {cpu_addr_q.part.offset[OFFSET_BIT_W-1:$clog2(CPU_BYTE_W)], {$clog2(CPU_BYTE_W){1'b0}}};
        end else begin
            assign cpu_addr_offset = '0;
        end
    endgenerate

    always_comb begin
        check_tag_d    = '0;
        lru_d          = lru_q;
        way0_valid_d   = way0_valid_q;
        way1_valid_d   = way1_valid_q;
        cpu_addr_d     = cpu_addr_q;
        cpu_we_d       = cpu_we_q;
        cpu_wbe_d      = cpu_wbe_q;
        cpu_wdata_d    = cpu_wdata_q;
        mem_req_cnt_d  = mem_req_cnt_q;
        mem_data_cnt_d = mem_data_cnt_q;

        if (mem_data_cnt_q.part.done) begin
            // no fill operation in progress

            if (mem_req_cnt_q.part.done) begin
                // no spill operation in progress

                // if there is a CPU request, schedule tag check for next cycle
                if (cpu_req_i & ~cache_miss) begin
                    check_tag_d     = 1'b1;
                    cpu_addr_d.addr = cpu_addr_i;
                    cpu_we_d        = cpu_we_i;
                    cpu_wbe_d       = cpu_be_i;
                    cpu_wdata_d     = cpu_wdata_i;
                end

                // update LRU way upon each tag check
                if (cache_hit) begin
                    // using way 0 makes way 1 LRU, using way 1 makes way 0 LRU
                    lru_d[cpu_addr_q.part.index] = tag_match_way0;
                end

                // start a spill or fill operation if a tag check failed (miss)
                if (cache_miss & ~hold_mem_i) begin
                    mem_req_cnt_d.val = mem_gnt_i ? 1 : '0;

                    if (~cache_spill) begin
                        mem_data_cnt_d.val = '0;
                    end
                end

            end else begin
                // a line spill operation is in progress

                if (mem_gnt_i) begin
                    mem_req_cnt_d.val = mem_req_cnt_q.val + 1;

                    // start refilling once the spill is done
                    if (mem_req_cnt_d.part.done) begin
                        mem_req_cnt_d.val  = '0;
                        mem_data_cnt_d.val = '0;
                    end
                end

            end

        end else begin
            // a line fill operation is in progress

            if (~lru_q[cpu_addr_q.part.index]) begin
                way0_valid_d[cpu_addr_q.part.index] = 1'b1;
            end else begin
                way1_valid_d[cpu_addr_q.part.index] = 1'b1;
            end

            if (~mem_req_cnt_q.part.done & mem_gnt_i) begin
                mem_req_cnt_d.val = mem_req_cnt_q.val + 1;
            end

            if (mem_rvalid_i) begin
                mem_data_cnt_d.val = mem_data_cnt_q.val + 1;

                if (mem_data_cnt_d.part.done) begin
                    check_tag_d = 1'b1;
                end
            end

        end
    end

    // convert CPU address to struct for easier access of relevant fields
    cpu_addr_t cpu_addr;
    assign cpu_addr.addr = cpu_addr_i;

    // Cache way interface signals
    assign way_rindex     = mem_data_cnt_q.part.done ? cpu_addr.part.index : cpu_addr_q.part.index;
    assign way_windex     = cpu_addr_q.part.index;
    assign way0_we        = mem_data_cnt_q.part.done ? (check_tag_q & tag_match_way0 & cpu_we_q) : ~lru_q[cpu_addr_q.part.index];
    assign way1_we        = mem_data_cnt_q.part.done ? (check_tag_q & tag_match_way1 & cpu_we_q) :  lru_q[cpu_addr_q.part.index];
    assign way_wtag       = cpu_addr_q.part.tag;
    assign way_wline_be   = mem_data_cnt_q.part.done ?
                            {{(LINE_BYTE_W - CPU_BYTE_W){1'b0}}, cpu_wbe_q         } << cpu_addr_offset :
                            {{(LINE_BYTE_W - MEM_BYTE_W){1'b0}}, {MEM_BYTE_W{1'b1}}} << (MEM_BYTE_W * mem_data_cnt_q.part.cnt);
    assign way_wline_data = mem_data_cnt_q.part.done ? {(LINE_BYTE_W / CPU_BYTE_W){cpu_wdata_q}} : {(LINE_BYTE_W / MEM_BYTE_W){mem_rdata_i}};
    assign way_wdirty     = mem_data_cnt_q.part.done & cpu_we_q;
    assign way_werr       = ~mem_data_cnt_q.part.done & mem_err_i;

    // CPU interface signals
    assign cpu_gnt_o    = mem_req_cnt_q.part.done & mem_data_cnt_q.part.done & ~cache_miss;
    assign cpu_rvalid_o = cache_hit; // & ~cpu_we_q;
    assign cpu_rdata_o  = tag_match_line[cpu_addr_offset * 8 +: CPU_BYTE_W * 8];
    assign cpu_err_o    = tag_match_err;

    // memory interface signals
    assign mem_req_o   = ~mem_req_cnt_q.part.done | cache_miss;
    assign mem_we_o    = (~mem_req_cnt_q.part.done & mem_data_cnt_q.part.done) | cache_spill;
    assign mem_addr_o  = {mem_we_o ? spill_tag : cpu_addr_q.part.tag, cpu_addr_q.part.index, mem_req_cnt_q.part.cnt, {$clog2(MEM_BYTE_W){1'b0}}};
    assign mem_wdata_o = spill_line[mem_req_cnt_q.part.cnt * MEM_BYTE_W * 8 +: MEM_BYTE_W * 8];

endmodule


module vproc_cache_way #(
        parameter int unsigned TAG_BIT_W   = 4,
        parameter int unsigned INDEX_BIT_W = 8,
        parameter int unsigned LINE_BYTE_W = 16
    )(
        input  logic                     clk_i,

        input  logic [INDEX_BIT_W-1:0]   windex_i,
        input  logic                     we_i,
        input  logic [TAG_BIT_W-1:0]     wtag_i,
        input  logic [LINE_BYTE_W-1:0]   wline_be_i,
        input  logic [LINE_BYTE_W*8-1:0] wline_data_i,
        input  logic                     wdirty_i,
        input  logic                     werr_i,

        input  logic [INDEX_BIT_W-1:0]   rindex_i,
        output logic [TAG_BIT_W-1:0]     rtag_o,
        output logic [LINE_BYTE_W*8-1:0] rline_o,
        output logic                     rdirty_o,
        output logic                     rerr_o
    );

    localparam int unsigned WAY_LEN = 2 ** INDEX_BIT_W;

    logic [TAG_BIT_W-1:0]     tags[WAY_LEN]  = '{default: '1};
    logic [LINE_BYTE_W*8-1:0] lines[WAY_LEN] = '{default: 128'h00112233445566778899AABBCCDDEEFF};
    logic [WAY_LEN-1:0]       dirty          = '0;
    logic [WAY_LEN-1:0]       err            = '0;

    always_ff @(posedge clk_i) begin
        rtag_o   <= tags [rindex_i];
        rline_o  <= lines[rindex_i];
        rdirty_o <= dirty[rindex_i];
        rerr_o   <= err  [rindex_i];

        if (we_i) begin
            tags [windex_i] <= wtag_i;
            dirty[windex_i] <= wdirty_i;
            err  [windex_i] <= werr_i;

            if (rindex_i == windex_i) begin
                rtag_o   <= wtag_i;
                rdirty_o <= wdirty_i;
                rerr_o   <= werr_i;
            end

            for (int i = 0; i < LINE_BYTE_W; i++) begin
                if (wline_be_i[i]) begin
                    lines[windex_i][8*i +: 8] <= wline_data_i[8*i +: 8];

                    if (rindex_i == windex_i) begin
                        rline_o[8*i +: 8] <= wline_data_i[8*i +: 8];
                    end
                end
            end

        end
    end

endmodule
