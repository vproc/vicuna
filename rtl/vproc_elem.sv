// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


`include "vproc_vregshift.svh"

module vproc_elem #(
        parameter int unsigned          VREG_W          = 128,  // width in bits of vector registers
        parameter int unsigned          VMSK_W          = 16,   // width of vector register masks (= VREG_W / 8)
        parameter int unsigned          CFG_VL_W        = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned          GATHER_OP_W     = 32,   // ELEM unit GATHER operand width in bits
        parameter int unsigned          XIF_ID_W        = 3,    // width in bits of instruction IDs
        parameter int unsigned          XIF_ID_CNT      = 8,    // total count of instruction IDs
        parameter int unsigned          MAX_WR_ATTEMPTS = 1,    // max required vregfile write attempts
        parameter bit                   BUF_VREG        = 1'b1, // insert pipeline stage after vreg read
        parameter bit                   BUF_RESULTS     = 1'b1, // insert pipeline stage after computing result
        parameter bit                   DONT_CARE_ZERO  = 1'b0  // initialize don't care values to zero
    )(
        input  logic                    clk_i,
        input  logic                    async_rst_ni,
        input  logic                    sync_rst_ni,

        input  logic [XIF_ID_W-1:0]     id_i,
        input  vproc_pkg::cfg_vsew      vsew_i,
        input  vproc_pkg::cfg_emul      emul_i,
        input  logic [CFG_VL_W-1:0]     vl_i,
        input  logic                    vl_0_i,

        input  logic                    op_rdy_i,
        output logic                    op_ack_o,

        input  vproc_pkg::op_mode_elem  mode_i,
        input  vproc_pkg::op_widenarrow widenarrow_i,
        input  vproc_pkg::op_regs       rs1_i,
        input  vproc_pkg::op_regs       rs2_i,
        input  logic [4:0]              vd_i,

        input  logic [31:0]             vreg_pend_wr_i,
        output logic [31:0]             vreg_pend_rd_o,
        input  logic [31:0]             vreg_pend_rd_i,

        output logic [31:0]             clear_wr_hazards_o,

        input  logic [XIF_ID_CNT-1:0]   instr_spec_i,
        input  logic [XIF_ID_CNT-1:0]   instr_killed_i,
        output logic                    instr_done_valid_o,
        output logic [XIF_ID_W-1:0]     instr_done_id_o,

        // connections to register file:
        input  logic [VREG_W-1:0]       vreg_mask_i,
        input  logic [VREG_W-1:0]       vreg_rd_i,
        output logic [4:0]              vreg_rd_addr_o,
        output logic [VREG_W-1:0]       vreg_wr_o,
        output logic [4:0]              vreg_wr_addr_o,
        output logic [VMSK_W-1:0]       vreg_wr_mask_o,
        output logic                    vreg_wr_en_o,

        // main core write-back signals:
        output logic                    xreg_valid_o,
        output logic [XIF_ID_W-1:0]     xreg_id_o,
        output logic [4:0]              xreg_addr_o,
        output logic [31:0]             xreg_data_o
    );

    import vproc_pkg::*;

    if ((GATHER_OP_W & (GATHER_OP_W - 1)) != 0 || GATHER_OP_W < 32 || GATHER_OP_W >= VREG_W) begin
        $fatal(1, "The vector GATHER operand width GATHER_OP_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", GATHER_OP_W);
    end

    if (MAX_WR_ATTEMPTS < 1 || (1 << (MAX_WR_ATTEMPTS - 1)) > VREG_W / 32) begin
        $fatal(1, "The maximum number of write attempts MAX_WR_ATTEMPTS of a unit ",
                  "must be at least 1 and 2^(MAX_WR_ATTEMPTS-1) must be less than or ",
                  "equal to the ratio of the vector register width vs the operand width ",
                  "of that unit.  ",
                  "For the vector ELEM unit MAX_WR_ATTEMPTS is %d and that ratio is %d.",
                  MAX_WR_ATTEMPTS, VREG_W / 32);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (MAX_WR_ATTEMPTS - 1)) - 1;


    ///////////////////////////////////////////////////////////////////////////
    // ELEM UNIT STATE:

    localparam int unsigned ELEM_CYCLES_PER_VREG   = VREG_W / 8;
    localparam int unsigned ELEM_COUNTER_W         = $clog2(ELEM_CYCLES_PER_VREG) + 3;

    localparam int unsigned GATHER_CYCLES_PER_VREG = VREG_W / GATHER_OP_W;
    localparam int unsigned GATHER_COUNTER_W       = $clog2(GATHER_CYCLES_PER_VREG);

    typedef union packed {
        logic [ELEM_COUNTER_W-1:0]     val;    // overall byte index
        struct packed {
            logic [2:0]                mul;    // mul part (vreg index)
            logic [ELEM_COUNTER_W-4:0] low;    // byte index in vreg (vreg pos)
        } part;
    } elem_counter;

    typedef struct packed {
        elem_counter                 count;
        logic [GATHER_COUNTER_W-1:0] count_gather;
        logic                        first_cycle;
        logic                        last_cycle;
        logic [XIF_ID_W-1:0]         id;
        logic                        requires_flush;
        op_mode_elem                 mode;
        cfg_vsew                     eew;         // effective element width
        cfg_emul                     emul;        // effective MUL factor
        logic [CFG_VL_W-1:0]         vl;
        logic                        vl_0;
        logic                        vl_mask;
        op_regs                      rs1;
        logic                        vs1_narrow;
        logic                        vs1_fetch;
        logic                        vs1_shift;
        op_regs                      rs2;
        logic                        gather_fetch;
        logic                        v0msk_fetch;
        logic [4:0]                  vd;
        logic                        vd_store;
    } elem_state;

    logic        state_valid_q,  state_valid_d;
    elem_state   state_q,        state_d;
    logic [31:0] vreg_pend_wr_q, vreg_pend_wr_d; // local copy of global vreg write mask
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_elem_state_valid
        if (~async_rst_ni) begin
            state_valid_q <= 1'b0;
        end
        else if (~sync_rst_ni) begin
            state_valid_q <= 1'b0;
        end else begin
            state_valid_q <= state_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_elem_state
        state_q        <= state_d;
        vreg_pend_wr_q <= vreg_pend_wr_d;
    end

    logic op_reduction;
    always_comb begin
        op_reduction = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (mode_i.op)
            ELEM_XMV:       op_reduction = 1'b0;
            ELEM_VPOPC:     op_reduction = 1'b0;
            ELEM_VFIRST:    op_reduction = 1'b0;
            ELEM_VID:       op_reduction = 1'b0;
            ELEM_VIOTA:     op_reduction = 1'b0;
            ELEM_VRGATHER:  op_reduction = 1'b0;
            ELEM_VCOMPRESS: op_reduction = 1'b0;
            ELEM_FLUSH:     op_reduction = 1'b0;
            ELEM_VREDSUM:   op_reduction = 1'b1;
            ELEM_VREDAND:   op_reduction = 1'b1;
            ELEM_VREDOR:    op_reduction = 1'b1;
            ELEM_VREDXOR:   op_reduction = 1'b1;
            ELEM_VREDMINU:  op_reduction = 1'b1;
            ELEM_VREDMIN:   op_reduction = 1'b1;
            ELEM_VREDMAXU:  op_reduction = 1'b1;
            ELEM_VREDMAX:   op_reduction = 1'b1;
            default: ;
        endcase
    end

    logic last_cycle;
    always_comb begin
        last_cycle = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (state_q.emul)
            EMUL_1: last_cycle =                                       (state_q.count.part.low == '1) & (state_q.count_gather == '1);
            EMUL_2: last_cycle = (state_q.count.part.mul[  0] == '1) & (state_q.count.part.low == '1) & (state_q.count_gather == '1);
            EMUL_4: last_cycle = (state_q.count.part.mul[1:0] == '1) & (state_q.count.part.low == '1) & (state_q.count_gather == '1);
            EMUL_8: last_cycle = (state_q.count.part.mul[2:0] == '1) & (state_q.count.part.low == '1) & (state_q.count_gather == '1);
            default: ;
        endcase
    end

    logic pipeline_ready;
    always_comb begin
        op_ack_o       = 1'b0;
        state_valid_d  = state_valid_q;
        state_d        = state_q;
        vreg_pend_wr_d = vreg_pend_wr_q & vreg_pend_wr_i;

        if (((~state_valid_q) | (last_cycle & pipeline_ready & ~state_q.requires_flush)) & op_rdy_i) begin
            op_ack_o               = 1'b1;
            state_d.count.val      = '0;
            state_d.count.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
            unique case (vsew_i)
                VSEW_8:  state_d.count.val[1:0] = 2'b00;
                VSEW_16: state_d.count.val[1:0] = 2'b01;
                VSEW_32: state_d.count.val[1:0] = 2'b11;
                default: ;
            endcase
            state_d.count_gather   = (mode_i.op == ELEM_VRGATHER) ? '0 : '1;
            state_valid_d          = 1'b1;
            state_d.first_cycle    = 1'b1;
            state_d.id             = id_i;
            state_d.requires_flush = (mode_i.op == ELEM_VCOMPRESS) | op_reduction;
            state_d.mode           = mode_i;
            state_d.eew            = vsew_i;
            state_d.emul           = emul_i;
            state_d.vl             = vl_i;
            state_d.vl_0           = vl_0_i;
            state_d.vl_mask        = ~vl_0_i;
            state_d.rs1            = ((mode_i.op == ELEM_XMV) | op_reduction) ? rs2_i : rs1_i;
            state_d.rs1.vreg       = ((mode_i.op == ELEM_XMV) | op_reduction) | rs1_i.vreg;
            state_d.vs1_narrow     = widenarrow_i == OP_WIDENING;
            state_d.vs1_fetch      = ((mode_i.op == ELEM_XMV) | op_reduction) | rs1_i.vreg;
            state_d.vs1_shift      = 1'b1;
            state_d.rs2            = op_reduction ? rs1_i : rs2_i;
            state_d.rs2.vreg       = rs2_i.vreg | op_reduction;
            state_d.gather_fetch   = 1'b1;
            state_d.v0msk_fetch    = 1'b1;
            state_d.vd             = vd_i;
            vreg_pend_wr_d         = vreg_pend_wr_i;
        end
        else if (state_valid_q & pipeline_ready) begin
            if (state_q.count_gather == '1) begin
                unique case (state_q.eew)
                    VSEW_8:  state_d.count.val = state_q.count.val + 1;
                    VSEW_16: state_d.count.val = state_q.count.val + 2;
                    VSEW_32: state_d.count.val = state_q.count.val + 4;
                    default: ;
                endcase
            end
            if (state_q.mode.op == ELEM_VRGATHER) begin
                state_d.count_gather = state_q.count_gather + 1;
            end
            if (last_cycle & state_q.requires_flush) begin
                state_d.count.val      = '0;
                state_d.count.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
                unique case (vsew_i)
                    VSEW_8:  state_d.count.val[1:0] = 2'b00;
                    VSEW_16: state_d.count.val[1:0] = 2'b01;
                    VSEW_32: state_d.count.val[1:0] = 2'b11;
                    default: ;
                endcase
                state_d.count.part.mul = '1; // flush only one vreg
                state_d.mode.op        = ELEM_FLUSH;
                state_d.requires_flush = 1'b0;
                state_d.rs1.vreg       = 1'b0;
            end
            state_valid_d        = ~last_cycle | state_q.requires_flush;
            state_d.first_cycle  = 1'b0;
            state_d.vs1_fetch    = 1'b0;
            state_d.gather_fetch = 1'b0;
            if (state_q.count_gather == '1) begin
                if (state_q.count.part.low == '1) begin
                    if (state_q.rs1.vreg & (~state_q.vs1_narrow | state_q.count.part.mul[0])) begin
                        state_d.rs1.r.vaddr[2:0] = state_q.rs1.r.vaddr[2:0] + 3'b1;
                        state_d.vs1_fetch        = state_q.rs1.vreg & ~last_cycle;
                    end
                end
                state_d.gather_fetch = 1'b1;
            end
            if (~state_q.vs1_narrow) begin
                state_d.vs1_shift = state_q.count.val[1:0] == '1;
            end else begin
                state_d.vs1_shift = state_q.count.val[2:0] == '1;
            end
            state_d.v0msk_fetch = 1'b0;
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // ELEM PIPELINE BUFFERS:

    // pass state information along pipeline:
    logic                        state_ex_ready,   state_res_ready,   state_vd_ready;
    logic      state_init_stall,                   state_res_stall;
    logic      state_init_valid, state_ex_valid_q, state_res_valid_q;
    elem_state state_init,       state_ex_q,       state_res_q;
    always_comb begin
        state_init_valid      = state_valid_q;
        state_init            = state_q;
        state_init.last_cycle = state_valid_q & last_cycle;
        state_init.vl_mask    = ~state_q.vl_0 & (state_q.count.val <= state_q.vl);
    end
    logic unpack_ready;
    assign pipeline_ready = unpack_ready & ~state_init_stall;

    // operands and result:
    //logic [31:0] elem_q,           elem_d;
    //logic        elem_idx_valid_q, elem_idx_valid_d;
    //logic        mask_q,           mask_d;
    //logic [31:0] redinit_q,        redinit_d;
    logic [31:0] result_q,         result_d;
    logic        result_mask_q,    result_mask_d;
    logic        result_valid_q,   result_valid_d;

    // track whether there are any valid results:
    logic        has_valid_result_q, has_valid_result_d;
    elem_counter vd_count_q,         vd_count_d;
    logic                            vd_store_d;
    logic [4:0]                      vd_vd_d;

    generate
        assign state_ex_ready = ~state_ex_valid_q | state_res_ready;

        if (BUF_RESULTS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_elem_stage_res_valid
                if (~async_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_res_valid_q <= 1'b0;
                end
                else if (state_res_ready) begin
                    state_res_valid_q <= state_ex_valid_q;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_elem_stage_res
                if (state_res_ready & state_ex_valid_q) begin
                    state_res_q    <= state_ex_q;
                    result_q       <= result_d;
                    result_mask_q  <= result_mask_d;
                    result_valid_q <= result_valid_d;
                end
            end
            assign state_res_ready = ~state_res_valid_q | (state_vd_ready & ~state_res_stall);
        end else begin
            always_comb begin
                state_res_valid_q = state_ex_valid_q;
                state_res_q       = state_ex_q;
                result_q          = result_d;
                result_mask_q     = result_mask_d;
                result_valid_q    = result_valid_d;
            end
            assign state_res_ready = state_vd_ready & ~state_res_stall;
        end

        always_ff @(posedge clk_i) begin
            if (state_vd_ready) begin
                vd_count_q         <= vd_count_d;
                has_valid_result_q <= has_valid_result_d;
            end
        end
    endgenerate

    logic [31:0] state_init_gather_vregs;
    always_comb begin
        state_init_gather_vregs = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_init.emul)
            EMUL_1: state_init_gather_vregs = 32'h01 <<  state_init.rs2.r.vaddr;
            EMUL_2: state_init_gather_vregs = 32'h03 << {state_init.rs2.r.vaddr[4:1], 1'b0};
            EMUL_4: state_init_gather_vregs = 32'h0F << {state_init.rs2.r.vaddr[4:2], 2'b0};
            EMUL_8: state_init_gather_vregs = 32'hFF << {state_init.rs2.r.vaddr[4:3], 3'b0};
            default: ;
        endcase
    end

    logic [31:0] pending_gather_vreg_reads_q, pending_gather_vreg_reads_d;
    always_ff @(posedge clk_i or negedge async_rst_ni) begin
        if (~async_rst_ni) begin
            pending_gather_vreg_reads_q <= '0;
        end
        else if (~sync_rst_ni) begin
            pending_gather_vreg_reads_q <= '0;
        end
        else begin
            pending_gather_vreg_reads_q <= pending_gather_vreg_reads_d;
        end
    end
    always_comb begin
        pending_gather_vreg_reads_d = pending_gather_vreg_reads_q;
        if (state_ex_valid_q & state_ex_q.last_cycle) begin
            pending_gather_vreg_reads_d = '0;
        end
        if (state_init_valid & ~state_init_stall & (state_init.mode.op == ELEM_VRGATHER)) begin
            pending_gather_vreg_reads_d |= state_init_gather_vregs;
        end
    end

    // Stall vreg reads until pending writes are complete; note that vreg read
    // stalling always happens in the init stage, since otherwise a substantial
    // amount of state would have to be forwarded (such as vreg_pend_wr_q)
    assign state_init_stall = (state_init.vs1_fetch                                                                 & vreg_pend_wr_q[state_init.rs1.r.vaddr]) |
                              (state_init.rs2.vreg & state_init.first_cycle & (state_init.mode.op != ELEM_VRGATHER) & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                              ((state_init.mode.op == ELEM_VRGATHER) & ((state_init_gather_vregs & vreg_pend_wr_q) != '0)) |
                              (state_init.v0msk_fetch & state_init.mode.masked & vreg_pend_wr_q[0]);

    // Stall xreg writes while the instruction is speculative
    assign state_res_stall = state_res_valid_q & state_res_q.mode.xreg & ((state_res_q.mode.op == ELEM_XMV) ? state_res_q.first_cycle : state_res_q.last_cycle) & instr_spec_i[state_res_q.id];

    // pending vreg reads
    // Note: The pipeline might stall while reading a vreg, hence a vreg has to
    // be part of the pending reads until the read is complete.
    logic [31:0] pend_vs1, pend_vs2;
    always_comb begin
        pend_vs1 = DONT_CARE_ZERO ? '0 : 'x;
        unique case ({state_init.emul, state_init.vs1_narrow})
            {EMUL_1, 1'b0}: pend_vs1 = 32'h01 <<  state_init.rs1.r.vaddr;
            {EMUL_2, 1'b1}: pend_vs1 = 32'h01 <<  state_init.rs1.r.vaddr;
            {EMUL_2, 1'b0}: pend_vs1 = 32'h03 << {state_init.rs1.r.vaddr[4:1], 1'b0};
            {EMUL_4, 1'b1}: pend_vs1 = 32'h03 << {state_init.rs1.r.vaddr[4:1], 1'b0};
            {EMUL_4, 1'b0}: pend_vs1 = 32'h0F << {state_init.rs1.r.vaddr[4:2], 2'b0};
            {EMUL_8, 1'b1}: pend_vs1 = 32'h0F << {state_init.rs1.r.vaddr[4:2], 2'b0};
            {EMUL_8, 1'b0}: pend_vs1 = 32'hFF << {state_init.rs1.r.vaddr[4:3], 3'b0};
            default: ;
        endcase
        // vs2 is either:
        //  - a mask vreg, which is always a single vreg read in the first cycle
        //  - the init vreg for reductions, which is also a single vreg read in the first cycle
        //    (for reductions vs1 and vs2 are swapped, so actually this is vs1)
        //  - the gather register group
        pend_vs2 = DONT_CARE_ZERO ? '0 : 'x;
        if (state_init.mode.op == ELEM_VRGATHER) begin
            // entire gather register group remains pending throughout the operation
            pend_vs2 = state_init_gather_vregs;
        end else begin
            // mask/init register is read right at the beginning
            pend_vs2 = state_init.first_cycle ? (32'h01 << state_init.rs2.r.vaddr) : '0;
        end
    end
    // Note: vs2 is read in the second cycle; the v0 mask has no extra buffer
    // and is always read in state_gather/state_vsm
    logic [31:0] unpack_pend_rd;
    assign vreg_pend_rd_o = ((
            ((state_init_valid & state_init.rs1.vreg   ) ? pend_vs1                        : '0) |
            ((state_init_valid & state_init.rs2.vreg   ) ? pend_vs2                        : '0) |
            ((state_init_valid & state_init.v0msk_fetch) ? {31'b0, state_init.mode.masked} : '0)
        ) & ~vreg_pend_wr_q) |
    pending_gather_vreg_reads_q | unpack_pend_rd;


    ///////////////////////////////////////////////////////////////////////////
    // ELEM REGISTER READ/WRITE:

    unpack_flags [3:0]       unpack_op_flags;
    logic        [3:0][4 :0] unpack_op_vaddr;
    logic        [3:0][31:0] unpack_op_xval;
    always_comb begin
        unpack_op_flags  [0]          = unpack_flags'('0);
        unpack_op_flags  [0].shift    = state_init.vs1_shift & state_init.gather_fetch;
        unpack_op_flags  [0].load     = state_init.vs1_fetch;
        unpack_op_flags  [0].hold     = ~state_init.gather_fetch;
        unpack_op_flags  [0].elemwise = '0;
        unpack_op_flags  [0].narrow   = state_init.vs1_narrow;
        unpack_op_flags  [0].sigext   = state_init.mode.sigext;
        unpack_op_vaddr  [0]          = state_init.rs1.r.vaddr;
        unpack_op_xval   [0]          = '0;
        unpack_op_flags  [1]          = unpack_flags'('0);
        unpack_op_flags  [1].shift    = DONT_CARE_ZERO ? '0 : 'x;
        case (state_init.eew)
            VSEW_8:  unpack_op_flags[1].shift = state_init.count[4:0] == '0;
            VSEW_16: unpack_op_flags[1].shift = state_init.count[5:0] == '0;
            VSEW_32: unpack_op_flags[1].shift = state_init.count[6:0] == '0;
            default: ;
        endcase
        unpack_op_flags  [1].load     = state_init.rs2.vreg & state_init.first_cycle & (state_init.mode.op != ELEM_VRGATHER);
        unpack_op_flags  [1].elemwise = '0;
        unpack_op_vaddr  [1]          = state_init.rs2.r.vaddr;
        unpack_op_xval   [1]          = '0;
        unpack_op_flags  [2]          = unpack_flags'('0);
        unpack_op_flags  [2].shift    = 1'b1;
        unpack_op_flags  [2].load     = state_init.gather_fetch & (state_init.mode.op == ELEM_VRGATHER);
        unpack_op_flags  [2].elemwise = '0;
        unpack_op_vaddr  [2]          = '0;
        unpack_op_xval   [2]          = '0;
        unpack_op_flags  [3]          = unpack_flags'('0);
        unpack_op_flags  [3].shift    = 1'b1;
        unpack_op_flags  [3].load     = state_init.v0msk_fetch & state_init.mode.masked;
        unpack_op_flags  [3].elemwise = '0;
        unpack_op_vaddr  [3]          = '0;
        unpack_op_xval   [3]          = '0;
    end

    localparam int unsigned UNPACK_VPORT_W [2] = '{VREG_W,VREG_W};
    localparam int unsigned UNPACK_VADDR_W [2] = '{5,5};
    localparam int unsigned UNPACK_OP_W    [4] = '{32,32,GATHER_OP_W,1};
    localparam int unsigned UNPACK_OP_STAGE[4] = '{1,2,3,3};
    localparam int unsigned UNPACK_OP_SRC  [4] = '{0,0,0,1};

    logic [3:0][GATHER_OP_W-1:0] unpack_ops;
    logic [1:0][4:0]             unpack_vreg_addr;
    logic [1:0][VREG_W-1:0]      unpack_vreg_data;
    vproc_vregunpack #(
        .MAX_VPORT_W          ( VREG_W                               ),
        .MAX_VADDR_W          ( 5                                    ),
        .VPORT_CNT            ( 2                                    ),
        .VPORT_W              ( UNPACK_VPORT_W                       ),
        .VADDR_W              ( UNPACK_VADDR_W                       ),
        .VPORT_ADDR_ZERO      ( 2'b10                                ),
        .VPORT_BUFFER         ( 2'b01                                ),
        .MAX_OP_W             ( GATHER_OP_W                          ),
        .OP_CNT               ( 4                                    ),
        .OP_W                 ( UNPACK_OP_W                          ),
        .OP_STAGE             ( UNPACK_OP_STAGE                      ),
        .OP_SRC               ( UNPACK_OP_SRC                        ),
        .OP_ADDR_OFFSET_OP0   ( 4'b0100                              ),
        .OP_MASK              ( 4'b1010                              ),
        .OP_XREG              ( 4'b0000                              ),
        .OP_NARROW            ( 4'b0001                              ),
        .OP_ALLOW_ELEMWISE    ( 4'b0000                              ),
        .OP_ALWAYS_ELEMWISE   ( 4'b1111                              ),
        .OP_HOLD_FLAG         ( 4'b0001                              ),
        .UNPACK_STAGES        ( 4                                    ),
        .FLAGS_T              ( unpack_flags                         ),
        .CTRL_DATA_W          ( $bits(elem_state)                    ),
        .DONT_CARE_ZERO       ( DONT_CARE_ZERO                       )
    ) elem_unpack (
        .clk_i                ( clk_i                                ),
        .async_rst_ni         ( async_rst_ni                         ),
        .sync_rst_ni          ( sync_rst_ni                          ),
        .vreg_rd_addr_o       ( unpack_vreg_addr                     ),
        .vreg_rd_data_i       ( unpack_vreg_data                     ),
        .pipe_in_valid_i      ( state_init_valid & ~state_init_stall ),
        .pipe_in_ready_o      ( unpack_ready                         ),
        .pipe_in_ctrl_i       ( state_init                           ),
        .pipe_in_eew_i        ( state_init.eew                       ),
        .pipe_in_op_flags_i   ( unpack_op_flags                      ),
        .pipe_in_op_vaddr_i   ( unpack_op_vaddr                      ),
        .pipe_in_op_xval_i    ( unpack_op_xval                       ),
        .pipe_out_valid_o     ( state_ex_valid_q                     ),
        .pipe_out_ready_i     ( state_ex_ready                       ),
        .pipe_out_ctrl_o      ( state_ex_q                           ),
        .pipe_out_op_data_o   ( unpack_ops                           ),
        .pending_vreg_reads_o ( unpack_pend_rd                       ),
        .stage_valid_any_o    (                                      ),
        .ctrl_flags_any_o     (                                      ),
        .ctrl_flags_all_o     (                                      )
    );
    assign vreg_rd_addr_o = unpack_vreg_addr[0];
    always_comb begin
        unpack_vreg_data[0] = vreg_rd_i;
        unpack_vreg_data[1] = vreg_mask_i;
    end
    logic [31:0]            elem_q;
    logic                   elem_idx_valid_q;
    logic                   mask_q;
    logic [31:0]            redinit_q;
    logic [GATHER_OP_W-1:0] gather_shift_q;
    logic [0:0]             v0msk_shift_q;
    assign elem_q           = unpack_ops[0][31:0];
    assign mask_q           = unpack_ops[1][0];
    assign redinit_q        = unpack_ops[1][31:0];
    assign gather_shift_q   = unpack_ops[2];
    assign v0msk_shift_q[0] = unpack_ops[3][0];

    logic [31:0] gather_byte_idx;
    always_comb begin
        gather_byte_idx = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex_q.eew)
            VSEW_8:  gather_byte_idx = {24'b0                               , elem_q[7 :0]       };
            VSEW_16: gather_byte_idx = {15'b0                               , elem_q[15:0], 1'b0 };
            VSEW_32: gather_byte_idx = {elem_q[31] | elem_q[30] | elem_q[29], elem_q[28:0], 2'b00};
            default: ;
        endcase
    end
    always_comb begin
        elem_idx_valid_q = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex_q.emul)
            EMUL_1: elem_idx_valid_q = gather_byte_idx[31:$clog2(VREG_W/8)  ] == '0;
            EMUL_2: elem_idx_valid_q = gather_byte_idx[31:$clog2(VREG_W/8)+1] == '0;
            EMUL_4: elem_idx_valid_q = gather_byte_idx[31:$clog2(VREG_W/8)+2] == '0;
            EMUL_8: elem_idx_valid_q = gather_byte_idx[31:$clog2(VREG_W/8)+3] == '0;
            default: ;
        endcase
    end

    // XREG write-back
    assign xreg_valid_o = state_res_valid_q & state_res_q.mode.xreg & ((state_res_q.mode.op == ELEM_XMV) ? state_res_q.first_cycle : state_res_q.last_cycle) &
                          ~state_res_stall & ~instr_killed_i[state_res_q.id];
    assign xreg_id_o    = state_res_q.id;
    assign xreg_addr_o  = state_res_q.vd;
    assign xreg_data_o  = result_q;

    // track whether there are any valid results
    always_comb begin
        has_valid_result_d = has_valid_result_q;
        if (state_res_q.first_cycle) begin
            has_valid_result_d = 1'b0;
        end
        if (result_valid_q) begin
            has_valid_result_d = 1'b1;
        end
    end

    // determine when we see the first valid result
    logic first_valid_result;
    assign first_valid_result = result_valid_q & (state_res_q.first_cycle | ~has_valid_result_q);

    always_comb begin
        vd_count_d.val = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_res_q.eew)
            VSEW_8:  vd_count_d.val = vd_count_q.val + {{(ELEM_COUNTER_W-1){1'b0}}, result_valid_q      };
            VSEW_16: vd_count_d.val = vd_count_q.val + {{(ELEM_COUNTER_W-2){1'b0}}, result_valid_q, 1'b0};
            VSEW_32: vd_count_d.val = vd_count_q.val + {{(ELEM_COUNTER_W-3){1'b0}}, result_valid_q, 2'b0};
            default: ;
        endcase
        if (first_valid_result) begin
            vd_count_d.val      = '0;
            vd_count_d.val[1:0] = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_res_q.eew)
                VSEW_8:  vd_count_d.val[1:0] = 2'b00;
                VSEW_16: vd_count_d.val[1:0] = 2'b01;
                VSEW_32: vd_count_d.val[1:0] = 2'b11;
                default: ;
            endcase
        end
    end
    assign vd_store_d = ~state_res_q.mode.xreg & result_valid_q & (vd_count_d.part.low == '1);
    always_comb begin
        vd_vd_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_res_q.emul)
            EMUL_1: vd_vd_d = state_res_q.vd;
            EMUL_2: vd_vd_d = state_res_q.vd | {4'b0, vd_count_d.part.mul[0:0]};
            EMUL_4: vd_vd_d = state_res_q.vd | {3'b0, vd_count_d.part.mul[1:0]};
            EMUL_8: vd_vd_d = state_res_q.vd | {2'b0, vd_count_d.part.mul[2:0]};
            default: ;
        endcase
    end

    elem_state state_pack;
    always_comb begin
        state_pack           = state_res_q;
        state_pack.count     = vd_count_d;
        state_pack.vd_store  = vd_store_d;
        state_pack.vd        = vd_vd_d;
    end

    logic pack_valid;
    assign pack_valid = state_res_valid_q & result_valid_q;
    pack_flags pack_res_flags;
    always_comb begin
        pack_res_flags       = pack_flags'('0);
        pack_res_flags.store = state_pack.vd_store;
        pack_res_flags.shift = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_pack.eew)
            VSEW_8:  pack_res_flags.shift = state_pack.count.val[1:0] == '0;
            VSEW_16: pack_res_flags.shift = state_pack.count.val[1:1] == '0;
            VSEW_32: pack_res_flags.shift = 1'b1;
            default: ;
        endcase
    end
    logic last_store;
    assign last_store = state_pack.last_cycle & ~state_pack.requires_flush & ~state_pack.mode.xreg;
    logic [1:0] pend_clear_cnt;
    assign pend_clear_cnt = state_pack.emul; // TODO reductions always have destination EMUL == 1
    vproc_vregpack #(
        .VPORT_W                     ( VREG_W                ),
        .VADDR_W                     ( 5                     ),
        .VPORT_WR_ATTEMPTS           ( MAX_WR_ATTEMPTS       ),
        .VPORT_PEND_CLR_BULK         ( 1'b1                  ),
        .RES_W                       ( 32                    ),
        .RES_MASK                    ( '0                    ),
        .RES_XREG                    ( '0                    ),
        .RES_NARROW                  ( '0                    ),
        .RES_ALLOW_ELEMWISE          ( '0                    ),
        .RES_ALWAYS_ELEMWISE         ( 1'b1                  ),
        .FLAGS_T                     ( pack_flags            ),
        .INSTR_ID_W                  ( XIF_ID_W              ),
        .INSTR_ID_CNT                ( XIF_ID_CNT            ),
        .DONT_CARE_ZERO              ( DONT_CARE_ZERO        )
    ) elem_pack (
        .clk_i                       ( clk_i                 ),
        .async_rst_ni                ( async_rst_ni          ),
        .sync_rst_ni                 ( sync_rst_ni           ),
        .pipe_in_valid_i             ( pack_valid            ),
        .pipe_in_ready_o             ( state_vd_ready        ),
        .pipe_in_instr_id_i          ( state_pack.id         ),
        .pipe_in_eew_i               ( state_pack.eew        ),
        .pipe_in_res_flags_i         ( pack_res_flags        ),
        .pipe_in_res_vaddr_i         ( state_pack.vd         ),
        .pipe_in_res_data_i          ( result_q              ),
        .pipe_in_res_mask_i          ( {4{result_mask_q}}    ),
        .pipe_in_pend_clear_i        ( last_store            ),
        .pipe_in_pend_clear_cnt_i    ( pend_clear_cnt        ),
        .pipe_in_instr_done_i        ( last_store            ),
        .vreg_wr_valid_o             ( vreg_wr_en_o          ),
        .vreg_wr_ready_i             ( 1'b1                  ),
        .vreg_wr_addr_o              ( vreg_wr_addr_o        ),
        .vreg_wr_be_o                ( vreg_wr_mask_o        ),
        .vreg_wr_data_o              ( vreg_wr_o             ),
        .pending_vreg_reads_i        ( vreg_pend_rd_i        ),
        .clear_pending_vreg_writes_o ( clear_wr_hazards_o    ),
        .instr_spec_i                ( instr_spec_i          ),
        .instr_killed_i              ( instr_killed_i        ),
        .instr_done_valid_o          ( instr_done_valid_o    ),
        .instr_done_id_o             ( instr_done_id_o       )
    );


    ///////////////////////////////////////////////////////////////////////////
    // ELEM OPERATION:

    logic [31:0] counter_q, counter_d;
    logic        counter_inc;
    always_ff @(posedge clk_i) begin
        counter_q <= counter_d;
    end
    assign counter_d = (state_ex_q.first_cycle ? 32'b0 : counter_q) + {31'b0, counter_inc};

    logic        v0msk;
    logic [31:0] reduct_val;
    assign v0msk      = v0msk_shift_q[0] | ~state_ex_q.mode.masked;
    assign reduct_val = state_ex_q.first_cycle ? redinit_q : result_q;
    always_comb begin
        counter_inc    = DONT_CARE_ZERO ? '0 : 'x;
        result_d       = DONT_CARE_ZERO ? '0 : 'x;
        result_mask_d  = DONT_CARE_ZERO ? '0 : 'x;
        result_valid_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_ex_q.mode.op)
            // move from vreg index 0 to xreg with sign extension
            ELEM_XMV: begin
                unique case (state_ex_q.eew)
                    VSEW_8:  result_d = {{24{elem_q[7 ]}}, elem_q[7 :0]};
                    VSEW_16: result_d = {{16{elem_q[15]}}, elem_q[15:0]};
                    VSEW_32: result_d =                    elem_q       ;
                    default: ;
                endcase
            end
            // vid writes each element's index to the destination vreg and can
            // be masked by v0
            ELEM_VID: begin
                counter_inc    = 1'b1;
                result_d       = state_ex_q.first_cycle ? '0 : counter_q;
                result_mask_d  = state_ex_q.vl_mask & v0msk;
                result_valid_d = 1'b1;
            end
            // vpopc and viota count the number of set bits in a mask vreg;
            // both can be masked by v0, in which case only unmasked elements
            // contribute to the sum and for viota only unmasked elements are
            // written
            ELEM_VPOPC,
            ELEM_VIOTA: begin
                counter_inc    = mask_q & state_ex_q.vl_mask & v0msk;
                result_d       = state_ex_q.first_cycle ? '0 : counter_q;
                result_mask_d  = state_ex_q.vl_mask & v0msk;
                result_valid_d = 1'b1;
            end
            // vfirst finds the index of the first set bit in a mask vreg and
            // returns -1 if there is none; can be masked by v0
            ELEM_VFIRST: begin
                counter_inc    = state_ex_q.first_cycle | (result_q[31] & ~mask_q);
                result_d       = state_ex_q.first_cycle ? {32{~mask_q}} : (result_q[31] & ~mask_q) ? '1 : counter_q;
                result_mask_d  = state_ex_q.vl_mask & v0msk;
                result_valid_d = 1'b1;
            end
            // vcompress packs elements for which the corresponding bit in a
            // mask vreg is set; cannot be masked by v0
            ELEM_VCOMPRESS: begin
                result_d       = elem_q;
                result_mask_d  = state_ex_q.vl_mask;
                result_valid_d = mask_q;
            end
            // vgather gathers elements from a vreg based on indices from a
            // second vreg; can be masked by v0
            ELEM_VRGATHER: begin
                result_d = (state_ex_q.count_gather == '0) ? '0 : result_q;
                //if (state_ex_q.count_gather == elem_q[$clog2(VREG_W/8)-1:$clog2(GATHER_OP_W/8)]) begin
                if (state_ex_q.count_gather == gather_byte_idx[$clog2(VREG_W/8)-1:$clog2(GATHER_OP_W/8)]) begin
                    result_d       = gather_shift_q[{{$clog2(VREG_W/GATHER_OP_W){1'b0}}, gather_byte_idx[$clog2(GATHER_OP_W/8)-1:0] & ({$clog2(GATHER_OP_W/8){1'b1}} << 2)} * 8 +: 32];
                    result_d[15:0] = gather_shift_q[{{$clog2(VREG_W/GATHER_OP_W){1'b0}}, gather_byte_idx[$clog2(GATHER_OP_W/8)-1:0] & ({$clog2(GATHER_OP_W/8){1'b1}} << 1)} * 8 +: 16];
                    result_d[7 :0] = gather_shift_q[{{$clog2(VREG_W/GATHER_OP_W){1'b0}}, gather_byte_idx[$clog2(GATHER_OP_W/8)-1:0] & ({$clog2(GATHER_OP_W/8){1'b1}}     )} * 8 +: 8 ];
                    if (~elem_idx_valid_q) begin
                        result_d = '0;
                    end
                end
                result_mask_d  = state_ex_q.vl_mask & v0msk;
                result_valid_d = state_ex_q.count_gather == '1;
            end
            // flush the destination register after a vcompress or reduction
            // (note that a flush might potentially write to more registers
            // than are part of the vreg group, but for these the write mask
            // will be all 0s)
            ELEM_FLUSH: begin
                result_mask_d  = 1'b0;
                result_valid_d = 1'b1;
            end

            // reduction operations
            // TODO support masked reductions (currently only unmasked)
            ELEM_VREDSUM: begin
                result_d       = state_ex_q.vl_mask ? (elem_q + reduct_val) : reduct_val;
                result_mask_d  = ~state_ex_q.vl_0;
                result_valid_d = state_ex_q.last_cycle;
            end
            ELEM_VREDAND: begin
                result_d       = state_ex_q.vl_mask ? (elem_q & reduct_val) : reduct_val;
                result_mask_d  = ~state_ex_q.vl_0;
                result_valid_d = state_ex_q.last_cycle;
            end
            ELEM_VREDOR: begin
                result_d       = state_ex_q.vl_mask ? (elem_q | reduct_val) : reduct_val;
                result_mask_d  = ~state_ex_q.vl_0;
                result_valid_d = state_ex_q.last_cycle;
            end
            ELEM_VREDXOR: begin
                result_d       = state_ex_q.vl_mask ? (elem_q ^ reduct_val) : reduct_val;
                result_mask_d  = ~state_ex_q.vl_0;
                result_valid_d = state_ex_q.last_cycle;
            end
            ELEM_VREDMINU: begin
                result_d = reduct_val;
                if (state_ex_q.vl_mask) begin
                    unique case (state_ex_q.eew)
                        VSEW_8:  result_d[7 :0] = (elem_q[7 :0] < reduct_val[7 :0]) ? elem_q[7 :0] : reduct_val[7 :0];
                        VSEW_16: result_d[15:0] = (elem_q[15:0] < reduct_val[15:0]) ? elem_q[15:0] : reduct_val[15:0];
                        VSEW_32: result_d       = (elem_q       < reduct_val      ) ? elem_q       : reduct_val      ;
                        default: ;
                    endcase
                end
                result_mask_d  = ~state_ex_q.vl_0;
                result_valid_d = state_ex_q.last_cycle;
            end
            ELEM_VREDMIN: begin
                result_d = reduct_val;
                if (state_ex_q.vl_mask) begin
                    unique case (state_ex_q.eew)
                        VSEW_8:  result_d[7 :0] = ($signed(elem_q[7 :0]) < $signed(reduct_val[7 :0])) ? elem_q[7 :0] : reduct_val[7 :0];
                        VSEW_16: result_d[15:0] = ($signed(elem_q[15:0]) < $signed(reduct_val[15:0])) ? elem_q[15:0] : reduct_val[15:0];
                        VSEW_32: result_d       = ($signed(elem_q      ) < $signed(reduct_val      )) ? elem_q       : reduct_val      ;
                        default: ;
                    endcase
                end
                result_mask_d  = ~state_ex_q.vl_0;
                result_valid_d = state_ex_q.last_cycle;
            end
            ELEM_VREDMAXU: begin
                result_d = reduct_val;
                if (state_ex_q.vl_mask) begin
                    unique case (state_ex_q.eew)
                        VSEW_8:  result_d[7 :0] = (elem_q[7 :0] > reduct_val[7 :0]) ? elem_q[7 :0] : reduct_val[7 :0];
                        VSEW_16: result_d[15:0] = (elem_q[15:0] > reduct_val[15:0]) ? elem_q[15:0] : reduct_val[15:0];
                        VSEW_32: result_d       = (elem_q       > reduct_val      ) ? elem_q       : reduct_val      ;
                        default: ;
                    endcase
                end
                result_mask_d  = ~state_ex_q.vl_0;
                result_valid_d = state_ex_q.last_cycle;
            end
            ELEM_VREDMAX: begin
                result_d = reduct_val;
                if (state_ex_q.vl_mask) begin
                    unique case (state_ex_q.eew)
                        VSEW_8:  result_d[7 :0] = ($signed(elem_q[7 :0]) > $signed(reduct_val[7 :0])) ? elem_q[7 :0] : reduct_val[7 :0];
                        VSEW_16: result_d[15:0] = ($signed(elem_q[15:0]) > $signed(reduct_val[15:0])) ? elem_q[15:0] : reduct_val[15:0];
                        VSEW_32: result_d       = ($signed(elem_q      ) > $signed(reduct_val      )) ? elem_q       : reduct_val      ;
                        default: ;
                    endcase
                end
                result_mask_d  = ~state_ex_q.vl_0;
                result_valid_d = state_ex_q.last_cycle;
            end
            default: ;

        endcase
    end


`ifdef VPROC_SVA
`include "vproc_elem_sva.svh"
`endif

endmodule
