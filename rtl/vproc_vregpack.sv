// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


// Packing results into vector registers
module vproc_vregpack #(
        // vector register port configuration
        parameter int unsigned               VPORT_W             = 0,    // vreg port widths
        parameter int unsigned               VADDR_W             = 5,    // address widths
        parameter int unsigned               VPORT_WR_ATTEMPTS   = 1,    // number of write attempts
        parameter bit                        VPORT_PEND_CLR_BULK = '0,   // clear pending wr in bulk

        // vector register result configuration
        parameter int unsigned               RES_W               = 0,    // result width
        parameter bit                        RES_MASK            = '0,   // result may be a mask
        parameter bit                        RES_XREG            = '0,   // result may be XREG
        parameter bit                        RES_NARROW          = '0,   // result may be narrow
        parameter bit                        RES_ALLOW_ELEMWISE  = '0,   // result may be 1 elem
        parameter bit                        RES_ALWAYS_ELEMWISE = '0,   // result is 1 elem

        parameter type                       FLAGS_T             = logic,// flags struct type
        parameter int unsigned               INSTR_ID_W          = 3,    // instruction IDs width
        parameter int unsigned               INSTR_ID_CNT        = 8,    // number of instr IDs
        parameter bit                        DONT_CARE_ZERO      = 1'b0  // set don't care 0
    )(
        input  logic                         clk_i,
        input  logic                         async_rst_ni,
        input  logic                         sync_rst_ni,

        // pipeline in
        input  logic                         pipe_in_valid_i,
        output logic                         pipe_in_ready_o,
        input  logic [INSTR_ID_W       -1:0] pipe_in_instr_id_i,       // ID of current instruction
        input  vproc_pkg::cfg_vsew           pipe_in_eew_i,            // current element width
        input  logic [VADDR_W          -1:0] pipe_in_vaddr_i,          // vreg address for writes
        input  logic                         pipe_in_res_valid_i,      // result is valid
        input  FLAGS_T                       pipe_in_res_flags_i,      // packing flags of result
        input  logic [RES_W            -1:0] pipe_in_res_data_i,       // result data
        input  logic [RES_W  /8        -1:0] pipe_in_res_mask_i,       // result mask
        input  logic                         pipe_in_pend_clear_i,     // clear pending writes
        input  logic [$clog2(VADDR_W-1)-1:0] pipe_in_pend_clear_cnt_i, // number of vregs to clear
        input  logic                         pipe_in_instr_done_i,     // instr done flag

        // vector register file write port
        output logic                         vreg_wr_valid_o,
        input  logic                         vreg_wr_ready_i,
        output logic [VADDR_W          -1:0] vreg_wr_addr_o,           // vreg write address
        output logic [VPORT_W/8        -1:0] vreg_wr_be_o,             // vreg write byte enable
        output logic [VPORT_W          -1:0] vreg_wr_data_o,           // vreg write data

        // pending vector register reads (writes stall if the destination register is not clear)
        input  logic [(1<<VADDR_W)     -1:0] pending_vreg_reads_i,

        // pending vector register writes clear mask
        output logic [(1<<VADDR_W)     -1:0] clear_pending_vreg_writes_o,

        // Instruction IDs speculative and killed masks (vector register writes stall while the ID
        // of the current instruction is speculative and are inhibited if it is killed)
        input  logic [INSTR_ID_CNT     -1:0] instr_spec_i,
        input  logic [INSTR_ID_CNT     -1:0] instr_killed_i,

        // Signals that this instruction ID is done
        output logic                         instr_done_valid_o,
        output logic [INSTR_ID_W       -1:0] instr_done_id_o
    );

    import vproc_pkg::*;

    if (VPORT_WR_ATTEMPTS < 1 || (1 << (VPORT_WR_ATTEMPTS - 1)) > VPORT_W / RES_W) begin
        $fatal(1, "The number of write attempts VPORT_WR_ATTEMPTS must be at least 1 and ",
                  "2^(VPORT_WR_ATTEMPTS-1) must be less than or equal to the ratio of the vector ",
                  "register port width vs the result width.  ",
                  "However, VPORT_WR_ATTEMPTS is %d and that ratio is %d.",
                  VPORT_WR_ATTEMPTS, VPORT_W / RES_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (VPORT_WR_ATTEMPTS - 1)) - 1;

    // width of the pending write vreg clear counter (choosen such that it can span up to 1/4 of the
    // vector register addresses)
    localparam int unsigned PEND_CLEAR_CNT_W = $clog2(VADDR_W-1);

    typedef struct packed {
        logic [INSTR_ID_W      -1:0] instr_id;
        cfg_vsew                     eew;
        logic [VADDR_W         -1:0] vaddr;
        FLAGS_T                      res_flags;
        logic [VPORT_W         -1:0] res_buffer;
        logic [VPORT_W/8       -1:0] msk_buffer;
        logic                        pend_clear;
        logic [PEND_CLEAR_CNT_W-1:0] pend_clear_cnt;
        logic                        instr_done;
    } vregpack_state_t;

    logic            stage_valid_q, stage_valid_d;
    vregpack_state_t stage_state_q, stage_state_d;
    logic            stage_stall;
    logic            stage_ready;
    always_ff @(posedge clk_i or negedge async_rst_ni) begin
        if (~async_rst_ni) begin
            stage_valid_q <= '0;
        end
        else if (~sync_rst_ni) begin
            stage_valid_q <= '0;
        end
        else begin
            stage_valid_q <= stage_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin
        stage_state_q <= stage_state_d;
    end

    logic [VPORT_W  -1:0] res_buffer, res_buffer_next;
    logic [VPORT_W/8-1:0] msk_buffer, msk_buffer_next;
    assign res_buffer = stage_state_q.res_buffer;
    assign msk_buffer = stage_state_q.msk_buffer;
    always_comb begin
        stage_valid_d = stage_valid_q;
        stage_state_d = stage_state_q;
        if (stage_ready) begin
            stage_valid_d                = pipe_in_valid_i;
            stage_state_d.instr_id       = pipe_in_instr_id_i;
            stage_state_d.eew            = pipe_in_eew_i;
            stage_state_d.vaddr          = pipe_in_vaddr_i;
            stage_state_d.res_flags      = pipe_in_res_flags_i;
            stage_state_d.pend_clear     = pipe_in_pend_clear_i;
            stage_state_d.pend_clear_cnt = pipe_in_pend_clear_cnt_i;
            stage_state_d.instr_done     = pipe_in_instr_done_i;
            if (pipe_in_res_valid_i) begin
                stage_state_d.res_buffer = res_buffer_next;
                stage_state_d.msk_buffer = msk_buffer_next;
            end
        end
    end

    assign stage_stall = stage_state_q.res_flags.store & (
        pending_vreg_reads_i[stage_state_q.vaddr] | instr_spec_i[stage_state_q.instr_id]
    );
    assign stage_ready = ~stage_valid_q | (
        (~stage_state_q.res_flags.store | vreg_wr_ready_i) & ~stage_stall
    );

    assign pipe_in_ready_o = stage_ready;

    assign instr_done_valid_o = stage_valid_q & stage_state_q.instr_done & ~stage_stall;
    assign instr_done_id_o    = stage_state_q.instr_id;

    localparam WRITE_BUFFER_SZ = (MAX_WR_DELAY > 0) ? MAX_WR_DELAY : 1;
    logic                        vreg_wr_en_q       [WRITE_BUFFER_SZ], vreg_wr_en_d;
    logic [VADDR_W         -1:0] vreg_wr_addr_q     [WRITE_BUFFER_SZ], vreg_wr_addr_d;
    logic [VPORT_W/8       -1:0] vreg_wr_mask_q     [WRITE_BUFFER_SZ], vreg_wr_mask_d;
    logic [VPORT_W         -1:0] vreg_wr_q          [WRITE_BUFFER_SZ], vreg_wr_d;
    logic                        vreg_wr_clear_q    [WRITE_BUFFER_SZ], vreg_wr_clear_d;
    logic [PEND_CLEAR_CNT_W-1:0] vreg_wr_clear_cnt_q[WRITE_BUFFER_SZ], vreg_wr_clear_cnt_d;
    always_ff @(posedge clk_i) begin
        vreg_wr_en_q       [0] <= vreg_wr_en_d;
        vreg_wr_addr_q     [0] <= vreg_wr_addr_d;
        vreg_wr_mask_q     [0] <= vreg_wr_mask_d;
        vreg_wr_q          [0] <= vreg_wr_d;
        vreg_wr_clear_q    [0] <= vreg_wr_clear_d;
        vreg_wr_clear_cnt_q[0] <= vreg_wr_clear_cnt_d;
        for (int i = 1; i < MAX_WR_DELAY; i++) begin
            vreg_wr_en_q       [i] <= vreg_wr_en_q       [i-1];
            vreg_wr_addr_q     [i] <= vreg_wr_addr_q     [i-1];
            vreg_wr_mask_q     [i] <= vreg_wr_mask_q     [i-1];
            vreg_wr_q          [i] <= vreg_wr_q          [i-1];
            vreg_wr_clear_q    [i] <= vreg_wr_clear_q    [i-1];
            vreg_wr_clear_cnt_q[i] <= vreg_wr_clear_cnt_q[i-1];
        end
    end

    assign vreg_wr_en_d        = stage_valid_q & stage_state_q.res_flags.store & ~stage_stall & ~instr_killed_i[stage_state_q.instr_id];
    assign vreg_wr_addr_d      = stage_state_q.vaddr;
    assign vreg_wr_d           = res_buffer;
    assign vreg_wr_mask_d      = msk_buffer;
    assign vreg_wr_clear_d     = stage_valid_q & stage_state_q.pend_clear & ~stage_stall;
    assign vreg_wr_clear_cnt_d = stage_state_q.pend_clear_cnt;

    always_comb begin
        vreg_wr_valid_o = vreg_wr_en_d;
        vreg_wr_addr_o  = vreg_wr_addr_d;
        vreg_wr_be_o    = vreg_wr_mask_d;
        vreg_wr_data_o  = vreg_wr_d;
        for (int i = 0; i < MAX_WR_DELAY; i++) begin
            if ((((i + 1) & (i + 2)) == 0) & vreg_wr_en_q[i]) begin
                vreg_wr_valid_o = 1'b1;
                vreg_wr_addr_o  = vreg_wr_addr_q[i];
                vreg_wr_be_o    = vreg_wr_mask_q[i];
                vreg_wr_data_o  = vreg_wr_q     [i];
            end
        end
    end

    // write hazard clearing
    logic [(1<<VADDR_W)-1:0] clear_wr_hazards_q, clear_wr_hazards_d;
    always_ff @(posedge clk_i) begin
        clear_wr_hazards_q <= clear_wr_hazards_d;
    end
    assign clear_pending_vreg_writes_o = clear_wr_hazards_q;

    logic                        pend_clear;
    logic [PEND_CLEAR_CNT_W-1:0] pend_clear_cnt;
    logic [VADDR_W         -1:0] pend_clear_addr;
    logic [VADDR_W         -1:0] pend_clear_addr_mask;
    assign pend_clear           = (MAX_WR_DELAY == 0) ? vreg_wr_clear_d     : vreg_wr_clear_q    [MAX_WR_DELAY-1];
    assign pend_clear_cnt       = (MAX_WR_DELAY == 0) ? vreg_wr_clear_cnt_d : vreg_wr_clear_cnt_q[MAX_WR_DELAY-1];
    assign pend_clear_addr      = (MAX_WR_DELAY == 0) ? vreg_wr_addr_d      : vreg_wr_addr_q     [MAX_WR_DELAY-1];
    assign pend_clear_addr_mask = {VADDR_W{1'b1}} << pend_clear_cnt;
    always_comb begin
        clear_wr_hazards_d = '0;
        if (pend_clear) begin
            if (VPORT_PEND_CLR_BULK) begin
                for (int i = 0; i < (1<<VADDR_W); i++) begin
                    clear_wr_hazards_d[i] = (VADDR_W'(i) & pend_clear_addr_mask) == (pend_clear_addr & pend_clear_addr_mask);
                end
            end else begin
                clear_wr_hazards_d[pend_clear_addr] = 1'b1;
            end
        end
    end


    logic [RES_W  -1:0] res_default;
    logic [RES_W/8-1:0] msk_default;
    always_comb begin
        res_default = pipe_in_res_data_i;
        msk_default = pipe_in_res_mask_i;
        // The result may be a byte mask in the lower RES_W/8 bits of pipe_in_res_data_i (with
        // the actual mask in pipe_in_res_mask_i becoming a bit mask in that case)
        if (RES_MASK & pipe_in_res_flags_i.mask) begin
            res_default = {pipe_in_res_data_i[RES_W/8-1:0], res_buffer[VPORT_W-1:VPORT_W-RES_W*7/8]};
        end
        else if ((RES_ALLOW_ELEMWISE & pipe_in_res_flags_i.elemwise) | RES_ALWAYS_ELEMWISE) begin
            unique case (pipe_in_eew_i)
                VSEW_8: begin
                    res_default = {pipe_in_res_data_i[7 :0]  , res_buffer[VPORT_W  -1:VPORT_W  -RES_W  +8 ]};
                    msk_default = {   pipe_in_res_mask_i[0]  , msk_buffer[VPORT_W/8-1:VPORT_W/8-RES_W/8+1 ]};
                end
                VSEW_16: begin
                    res_default = {pipe_in_res_data_i[15:0]  , res_buffer[VPORT_W  -1:VPORT_W  -RES_W  +16]};
                    msk_default = {{2{pipe_in_res_mask_i[0]}}, msk_buffer[VPORT_W/8-1:VPORT_W/8-RES_W/8+2 ]};
                end
                VSEW_32: begin
                    res_default = {pipe_in_res_data_i[31:0]  , {RES_W  -32{1'b0}}} | (res_buffer[VPORT_W  -1 -: RES_W  ] >> 32);
                    msk_default = {{4{pipe_in_res_mask_i[0]}}, {RES_W/8-4 {1'b0}}} | (msk_buffer[VPORT_W/8-1 -: RES_W/8] >> 4 );
                end
                default: ;
            endcase
        end
        else if (RES_NARROW & pipe_in_res_flags_i.narrow) begin
            res_default = {pipe_in_res_data_i[RES_W/2 -1:0], res_buffer[VPORT_W-1:VPORT_W-RES_W/2 ]};
            msk_default = {pipe_in_res_mask_i[RES_W/16-1:0], res_buffer[VPORT_W-1:VPORT_W-RES_W/16]};
        end
    end

    always_comb begin
        // by default, retain current value for lower part and assign default value for upper part
        res_buffer_next = {res_default, res_buffer[VPORT_W  -RES_W  -1:0]};
        msk_buffer_next = {msk_default, msk_buffer[VPORT_W/8-RES_W/8-1:0]};
        // shift signal shifts entire content right by the width of the result; full-size results
        // shift every cycle
        if ((~RES_MASK & ~RES_NARROW & ~RES_ALLOW_ELEMWISE & ~RES_ALWAYS_ELEMWISE) |
            pipe_in_res_flags_i.shift
        ) begin
            res_buffer_next[VPORT_W  -RES_W  -1:0] = res_buffer[VPORT_W  -1:RES_W  ];
            msk_buffer_next[VPORT_W/8-RES_W/8-1:0] = msk_buffer[VPORT_W/8-1:RES_W/8];
        end
    end

endmodule
