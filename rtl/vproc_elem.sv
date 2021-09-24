// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


`include "vproc_vregshift.svh"

module vproc_elem #(
        parameter int unsigned         VREG_W,               // width in bits of vector registers
        parameter int unsigned         VMSK_W,               // width of vector register masks (= VREG_W / 8)
        parameter int unsigned         CFG_VL_W,
        parameter int unsigned         GATHER_OP_W,
        parameter int unsigned         MAX_WR_ATTEMPTS = 1,
        parameter bit                  BUF_VREG        = 1'b1,
        parameter bit                  BUF_RESULTS     = 1'b1, // buffer result in registers
        parameter bit                  COMB_INIT_ZERO  = 1'b0,
        parameter bit                  ASYNC_RESET     = 1'b0
    )(
        input  logic                   clk_i,
        input  logic                   rst_ni,

        input  vproc_pkg::cfg_vsew     vsew_i,
        input  vproc_pkg::cfg_lmul     lmul_i,
        input  logic [CFG_VL_W-1:0]    vl_i,
        input  logic                   vl_0_i,

        input  logic                   op_rdy_i,
        output logic                   op_ack_o,

        input  vproc_pkg::op_mode_elem mode_i,
        input  logic [4:0]             vs1_i,
        input  logic                   vs1_vreg_i,
        input  logic [4:0]             vs2_i,
        input  logic                   vs2_vreg_i,
        input  logic [4:0]             vd_i,

        output logic [31:0]            clear_rd_hazards_o,
        output logic [31:0]            clear_wr_hazards_o,

        // connections to register file:
        input  logic [VREG_W-1:0]      vreg_mask_i,
        input  logic [VREG_W-1:0]      vreg_rd_i,
        output logic [4:0]             vreg_rd_addr_o,
        output logic [VREG_W-1:0]      vreg_wr_o,
        output logic [4:0]             vreg_wr_addr_o,
        output logic [VMSK_W-1:0]      vreg_wr_mask_o,
        output logic                   vreg_wr_en_o,

        // main core write-back signals:
        output logic                   xreg_valid_o,
        output logic [31:0]            xreg_o
    );

    import vproc_pkg::*;

    if ((GATHER_OP_W & (GATHER_OP_W - 1)) != 0 || GATHER_OP_W < 32 || GATHER_OP_W >= VREG_W) begin
        $fatal(1, "The vector GATHER operand width GATHER_OP_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", GATHER_OP_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << MAX_WR_ATTEMPTS) - 1;


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
        elem_counter                 count_store;
        logic                        busy;
        logic                        first_cycle;
        logic                        last_cycle;
        logic                        requires_flush;
        op_mode_elem                 mode;
        cfg_vsew                     eew;         // effective element width
        cfg_emul                     emul;        // effective MUL factor
        logic [CFG_VL_W-1:0]         vl;
        logic                        vl_0;
        logic                        vl_mask;
        logic [4:0]                  vs1;
        logic                        vs1_vreg;
        logic                        vs1_fetch;
        logic                        vs1_shift;
        logic [4:0]                  vs2;
        logic                        vs2_vreg;
        logic                        gather_fetch;
        logic [4:0]                  vd;
        logic                        vd_store;
    } elem_state;

    elem_state state_q, state_d;

    generate
        if (ASYNC_RESET) begin
            always_ff @(posedge clk_i or negedge rst_ni) begin : vproc_elem_state
                if (!rst_ni) begin
                    state_q <= '{busy: 1'b0, default: 'x};
                end else begin
                    state_q <= state_d;
                end
            end
        end else begin
            always_ff @(posedge clk_i) begin : vproc_elem_state
                state_q          <= state_d;
                if (!rst_ni) begin
                    state_q.busy <= 1'b0;
                end
            end
        end
    endgenerate

    logic op_reduction;
    always_comb begin
        op_reduction = COMB_INIT_ZERO ? 1'b0 : 1'bx;
        case (mode_i.op)
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
        endcase
    end

    logic last_cycle;
    always_comb begin
        last_cycle = COMB_INIT_ZERO ? 1'b0 : 1'bx;
        unique case (state_q.emul)
            EMUL_1: last_cycle =                                       (state_q.count.part.low == '1) & (state_q.count_gather == '1);
            EMUL_2: last_cycle = (state_q.count.part.mul[  0] == '1) & (state_q.count.part.low == '1) & (state_q.count_gather == '1);
            EMUL_4: last_cycle = (state_q.count.part.mul[1:0] == '1) & (state_q.count.part.low == '1) & (state_q.count_gather == '1);
            EMUL_8: last_cycle = (state_q.count.part.mul[2:0] == '1) & (state_q.count.part.low == '1) & (state_q.count_gather == '1);
        endcase
    end

    always_comb begin
        op_ack_o = 1'b0;
        state_d  = state_q;

        if (((~state_q.busy) | (last_cycle & ~state_q.requires_flush)) & op_rdy_i) begin
            op_ack_o               = 1'b1;
            state_d.count.val      = '0;
            state_d.count.val[1:0] = COMB_INIT_ZERO ? '0 : 'x;
            case (vsew_i)
                VSEW_8:  state_d.count.val[1:0] = 2'b00;
                VSEW_16: state_d.count.val[1:0] = 2'b01;
                VSEW_32: state_d.count.val[1:0] = 2'b11;
            endcase
            state_d.count_gather   = (mode_i.op == ELEM_VRGATHER) ? '0 : '1;
            state_d.busy           = 1'b1;
            state_d.first_cycle    = 1'b1;
            state_d.requires_flush = (mode_i.op == ELEM_VCOMPRESS) | op_reduction;
            state_d.mode           = mode_i;
            state_d.eew            = vsew_i;
            state_d.emul = COMB_INIT_ZERO ? cfg_emul'('0) : cfg_emul'('x);
            unique case (lmul_i)
                LMUL_F8,
                LMUL_F4,
                LMUL_F2,
                LMUL_1: state_d.emul = EMUL_1;
                LMUL_2: state_d.emul = EMUL_2;
                LMUL_4: state_d.emul = EMUL_4;
                LMUL_8: state_d.emul = EMUL_8;
            endcase
            state_d.vl             = vl_i;
            state_d.vl_0           = vl_0_i;
            state_d.vl_mask        = ~vl_0_i;
            state_d.vs1            = ((mode_i.op == ELEM_XMV) | op_reduction) ? vs2_i : vs1_i;
            state_d.vs1_vreg       = ((mode_i.op == ELEM_XMV) | op_reduction) | vs1_vreg_i;
            state_d.vs1_fetch      = ((mode_i.op == ELEM_XMV) | op_reduction) | vs1_vreg_i;
            state_d.vs1_shift      = 1'b1;
            state_d.vs2            = op_reduction ? vs1_i : vs2_i;
            state_d.vs2_vreg       = vs2_vreg_i | op_reduction;
            state_d.gather_fetch   = 1'b1;
            state_d.vd             = vd_i;
        end
        else if (state_q.busy) begin
            if (state_q.count_gather == '1) begin
                case (state_q.eew)
                    VSEW_8:  state_d.count.val = state_q.count.val + 1;
                    VSEW_16: state_d.count.val = state_q.count.val + 2;
                    VSEW_32: state_d.count.val = state_q.count.val + 4;
                endcase
            end
            if (state_q.mode.op == ELEM_VRGATHER) begin
                state_d.count_gather = state_q.count_gather + 1;
            end
            if (last_cycle & state_q.requires_flush) begin
                state_d.count.val      = '0;
                state_d.count.val[1:0] = COMB_INIT_ZERO ? '0 : 'x;
                case (vsew_i)
                    VSEW_8:  state_d.count.val[1:0] = 2'b00;
                    VSEW_16: state_d.count.val[1:0] = 2'b01;
                    VSEW_32: state_d.count.val[1:0] = 2'b11;
                endcase
                state_d.count.part.mul = '1; // flush only one vreg
                state_d.mode.op        = ELEM_FLUSH;
                state_d.requires_flush = 1'b0;
                state_d.vs1_vreg       = 1'b0;
            end
            state_d.busy         = ~last_cycle | state_q.requires_flush;
            state_d.first_cycle  = 1'b0;
            state_d.vs1_fetch    = 1'b0;
            state_d.gather_fetch = 1'b0;
            if (state_q.count_gather == '1) begin
                if (state_q.count.part.low == '1) begin
                    state_d.vs1[2:0]  = state_q.vs1[2:0] + 3'b1;
                    state_d.vs1_fetch = state_q.vs1_vreg & ~last_cycle;
                end
                state_d.gather_fetch = 1'b1;
            end
            state_d.vs1_shift = state_q.count.val[1:0] == '1;
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // ELEM PIPELINE BUFFERS:

    // pass state information along pipeline:
    elem_state state_init, state_vreg_q, state_vs1_q, state_vsm_q, state_gather_q, state_ex_q, state_res_q, state_vd_q;
    always_comb begin
        state_init            = state_q;
        state_init.last_cycle = state_q.busy & last_cycle;
        state_init.vl_mask    = ~state_q.vl_0 & (state_q.count.val <= state_q.vl);
    end
    elem_counter count_store_d;
    logic        vd_store_d;

    // vreg read register:
    logic [VREG_W-1:0] vreg_rd_q, vreg_rd_d;

    // operand shift register:
    logic [VREG_W-1:0] vs1_shift_q,    vs1_shift_d;
    logic [VREG_W-1:0] vsm_shift_q,    vsm_shift_d;
    logic [VREG_W-1:0] gather_shift_q, gather_shift_d;
    logic [VREG_W-1:0] v0msk_shift_q,  v0msk_shift_d;

    // temporary buffer for vs1 while fetching vsm:
    logic [31:0] vs1_tmp_q, vs1_tmp_d;

    // temporary buffers for elem, mask, and reduct init while fetching gather:
    logic [31:0] elem_tmp_q,    elem_tmp_d;
    logic        mask_tmp_q,    mask_tmp_d;
    logic [31:0] redinit_tmp_q, redinit_tmp_d;

    // operands and result:
    logic [31:0] elem_q,           elem_d;
    logic        elem_idx_valid_q, elem_idx_valid_d;
    logic        mask_q,           mask_d;
    logic [31:0] redinit_q,        redinit_d;
    logic [31:0] result_q,         result_d;
    logic        result_mask_q,    result_mask_d;
    logic        result_valid_q,   result_valid_d;

    // first valid result register:
    logic first_valid_result_q, first_valid_result_d;

    // result shift register:
    logic [VREG_W-1:0] vd_shift_q,    vd_shift_d;
    logic [VMSK_W-1:0] vdmsk_shift_q, vdmsk_shift_d;

    // vreg write buffers
    logic              vreg_wr_en_q  [MAX_WR_DELAY], vreg_wr_en_d;
    logic [4:0]        vreg_wr_addr_q[MAX_WR_DELAY], vreg_wr_addr_d;
    logic [VMSK_W-1:0] vreg_wr_mask_q[MAX_WR_DELAY], vreg_wr_mask_d;
    logic [VREG_W-1:0] vreg_wr_q     [MAX_WR_DELAY], vreg_wr_d;
    logic              vreg_wr_last_q[MAX_WR_DELAY], vreg_wr_last_d;
    logic [4:0]        vreg_wr_base_q[MAX_WR_DELAY], vreg_wr_base_d;
    cfg_emul           vreg_wr_emul_q[MAX_WR_DELAY], vreg_wr_emul_d;

    // hazard clear registers
    logic [31:0] clear_rd_hazards_q, clear_rd_hazards_d;
    logic [31:0] clear_wr_hazards_q, clear_wr_hazards_d;

    generate
        if (BUF_VREG) begin
            always_ff @(posedge clk_i) begin : vproc_elem_stage_vreg
                state_vreg_q <= state_init;
                vreg_rd_q    <= vreg_rd_d;
            end
        end else begin
            always_comb begin
                state_vreg_q = state_init;
                vreg_rd_q    = vreg_rd_d;
            end
        end

        always_ff @(posedge clk_i) begin : vproc_elem_stage_vs1
            state_vs1_q <= state_vreg_q;
            vs1_shift_q <= vs1_shift_d;
        end

        always_ff @(posedge clk_i) begin : vproc_elem_stage_vsm
            state_vsm_q   <= state_vs1_q;
            vs1_tmp_q     <= vs1_tmp_d;
            vsm_shift_q   <= vsm_shift_d;
        end

        if (BUF_VREG) begin
            always_ff @(posedge clk_i) begin : vproc_elem_stage_gather
                state_gather_q <= state_vsm_q;
                elem_tmp_q     <= elem_tmp_d;
                mask_tmp_q     <= mask_tmp_d;
                redinit_tmp_q  <= redinit_tmp_d;
            end
        end else begin
            always_comb begin
                state_gather_q = state_vsm_q;
                elem_tmp_q     = elem_tmp_d;
                mask_tmp_q     = mask_tmp_d;
                redinit_tmp_q  = redinit_tmp_d;
            end
        end

        always_ff @(posedge clk_i) begin : vproc_elem_stage_ex
            state_ex_q       <= state_gather_q;
            elem_q           <= elem_d;
            elem_idx_valid_q <= elem_idx_valid_d;
            mask_q           <= mask_d;
            redinit_q        <= redinit_d;
            gather_shift_q   <= gather_shift_d;
            v0msk_shift_q    <= v0msk_shift_d;
        end

        if (BUF_RESULTS) begin
            always_ff @(posedge clk_i) begin : vproc_elem_stage_res
                state_res_q    <= state_ex_q;
                result_q       <= result_d;
                result_mask_q  <= result_mask_d;
                result_valid_q <= result_valid_d;
            end
        end else begin
            always_comb begin
                state_res_q    = state_ex_q;
                result_q       = result_d;
                result_mask_q  = result_mask_d;
                result_valid_q = result_valid_d;
            end
        end

        always_ff @(posedge clk_i) begin : vproc_elem_stage_vd
            state_vd_q             <= state_res_q;
            state_vd_q.count_store <= count_store_d;
            state_vd_q.vd_store    <= vd_store_d;
            vd_shift_q             <= vd_shift_d;
            vdmsk_shift_q          <= vdmsk_shift_d;
            first_valid_result_q   <= first_valid_result_d;
        end

        if (MAX_WR_DELAY > 0) begin
            always_ff @(posedge clk_i) begin : vproc_elem_wr_delay
                vreg_wr_en_q  [0] = vreg_wr_en_d;
                vreg_wr_addr_q[0] = vreg_wr_addr_d;
                vreg_wr_mask_q[0] = vreg_wr_mask_d;
                vreg_wr_q     [0] = vreg_wr_d;
                vreg_wr_last_q[0] = vreg_wr_last_d;
                vreg_wr_base_q[0] = vreg_wr_base_d;
                vreg_wr_emul_q[0] = vreg_wr_emul_d;
                for (int i = 1; i < MAX_WR_DELAY; i++) begin
                    vreg_wr_en_q  [i] = vreg_wr_en_q  [i-1];
                    vreg_wr_addr_q[i] = vreg_wr_addr_q[i-1];
                    vreg_wr_mask_q[i] = vreg_wr_mask_q[i-1];
                    vreg_wr_q     [i] = vreg_wr_q     [i-1];
                    vreg_wr_last_q[i] = vreg_wr_last_q[i-1];
                    vreg_wr_base_q[i] = vreg_wr_base_q[i-1];
                    vreg_wr_emul_q[i] = vreg_wr_emul_q[i-1];
                end
            end
        end

        always_ff @(posedge clk_i) begin
            clear_rd_hazards_q <= clear_rd_hazards_d;
            clear_wr_hazards_q <= clear_wr_hazards_d;
        end
    endgenerate

    always_comb begin
        vreg_wr_en_o   = vreg_wr_en_d;
        vreg_wr_addr_o = vreg_wr_addr_d;
        vreg_wr_mask_o = vreg_wr_mask_d;
        vreg_wr_o      = vreg_wr_d;
        for (int i = 0; i < MAX_WR_DELAY; i++) begin
            if ((((i + 1) & (i + 2)) == 0) & vreg_wr_en_q[i]) begin
                vreg_wr_en_o   = 1'b1;
                vreg_wr_addr_o = vreg_wr_addr_q[i];
                vreg_wr_mask_o = vreg_wr_mask_q[i];
                vreg_wr_o      = vreg_wr_q     [i];
            end
        end
    end

    // write hazard clearing
    always_comb begin
        if (MAX_WR_DELAY == 0) begin
            clear_wr_hazards_d = COMB_INIT_ZERO ? '0 : 'x;
            unique case (vreg_wr_emul_d)
                EMUL_1: clear_wr_hazards_d = 32'h00000001 << {vreg_wr_base_d                           };
                EMUL_2: clear_wr_hazards_d = 32'h00000003 << {vreg_wr_base_d                [4:1], 1'b0};
                EMUL_4: clear_wr_hazards_d = 32'h0000000F << {vreg_wr_base_d                [4:2], 2'b0};
                EMUL_8: clear_wr_hazards_d = 32'h000000FF << {vreg_wr_base_d                [4:3], 3'b0};
            endcase
            if (~vreg_wr_last_d) begin
                clear_wr_hazards_d = '0;
            end
        end else begin
            unique case (vreg_wr_emul_q[MAX_WR_DELAY-1])
                EMUL_1: clear_wr_hazards_d = 32'h00000001 << {vreg_wr_base_q[MAX_WR_DELAY-1]           };
                EMUL_2: clear_wr_hazards_d = 32'h00000003 << {vreg_wr_base_q[MAX_WR_DELAY-1][4:1], 1'b0};
                EMUL_4: clear_wr_hazards_d = 32'h0000000F << {vreg_wr_base_q[MAX_WR_DELAY-1][4:2], 2'b0};
                EMUL_8: clear_wr_hazards_d = 32'h000000FF << {vreg_wr_base_q[MAX_WR_DELAY-1][4:3], 3'b0};
            endcase
            if (~vreg_wr_last_q[MAX_WR_DELAY-1]) begin
                clear_wr_hazards_d = '0;
            end
        end
    end
    assign clear_wr_hazards_o = clear_wr_hazards_q;

    // read hazard clearing
    logic [31:0] gather_hazard;
    always_comb begin
        gather_hazard = COMB_INIT_ZERO ? '0 : 'x;
        unique case (state_gather_q.emul)
            EMUL_1: gather_hazard = (32'h00000001 <<  state_gather_q.vs2              );
            EMUL_2: gather_hazard = (32'h00000003 << {state_gather_q.vs2[4:1], 1'b0  });
            EMUL_4: gather_hazard = (32'h0000000F << {state_gather_q.vs2[4:2], 2'b00 });
            EMUL_8: gather_hazard = (32'h000000FF << {state_gather_q.vs2[4:3], 3'b000});
        endcase
    end
    // vs2 is either a mask vreg or it is the gather register group, which has to be cleared as a whole in the last cycle
    assign clear_rd_hazards_d = (
        ((state_init.busy     & state_init.vs1_fetch                                                                         ) ? (32'b1 << state_init.vs1  ) : 32'b0) |
        ((state_vreg_q.busy   & state_vreg_q.first_cycle  & state_vreg_q.vs2_vreg & (state_vreg_q.mode.op   != ELEM_VRGATHER)) ? (32'b1 << state_vreg_q.vs2) : 32'b0) |
        ((state_gather_q.busy & state_gather_q.last_cycle &                         (state_gather_q.mode.op == ELEM_VRGATHER)) ? gather_hazard               : 32'b0) |
        {31'b0, state_init.busy & state_init.mode.masked & state_init.first_cycle}
    );
    assign clear_rd_hazards_o = clear_rd_hazards_q;


    ///////////////////////////////////////////////////////////////////////////
    // ELEM REGISTER READ/WRITE:

    // source register addressing and read:
    //assign vreg_rd_addr_o = state_init.vs1_fetch ? state_init.vs1 : state_init.vs2;
    always_comb begin
        vreg_rd_addr_o = COMB_INIT_ZERO ? '0 : 'x;
        // fetch vs1 when the corresponding flag is set
        if (state_init.vs1_fetch) begin
            vreg_rd_addr_o = state_init.vs1;
        end
        // fetch vs2 in the cycle following vs1 (used as mask for mask and
        // permutation instructions and as initalization element in reductions)
        else if (state_vreg_q.mode.op != ELEM_VRGATHER) begin
            vreg_rd_addr_o = BUF_VREG ? state_vreg_q.vs2 : state_vs1_q.vs2;
        end
        // otherwise fetch the register corresponding to the gather index
        else begin
            vreg_rd_addr_o = state_vsm_q.vs2 | {2'b0, vs1_tmp_q[$clog2(VREG_W/8)+2:$clog2(VREG_W/8)]};
        end
    end
    assign vreg_rd_d = vreg_rd_i;

    // operand shift registers assignment:
    fetch_info vs1_info;
    always_comb begin
        vs1_info.shift  = state_vreg_q.vs1_shift & state_vreg_q.gather_fetch;
        vs1_info.fetch  = state_vreg_q.vs1_fetch;
    end
    `VREGSHIFT_OPERAND_VSEW(VREG_W, 32, vs1_info, ~state_vreg_q.gather_fetch, state_vreg_q.eew, vreg_rd_q, vs1_shift_q, vs1_shift_d)

    always_comb begin
        vs1_tmp_d = vs1_shift_q[31:0];
        if (state_vs1_q.mode.op == ELEM_VRGATHER) begin
            case (state_vs1_q.eew)
                VSEW_8:  vs1_tmp_d = {24'b0                                              , vs1_shift_q[7 :0]       };
                VSEW_16: vs1_tmp_d = {15'b0                                              , vs1_shift_q[15:0], 1'b0 };
                VSEW_32: vs1_tmp_d = {vs1_shift_q[31] | vs1_shift_q[30] | vs1_shift_q[29], vs1_shift_q[28:0], 2'b00};
            endcase
        end
        vsm_shift_d = vreg_rd_q;
        if (~state_vs1_q.first_cycle) begin
            vsm_shift_d[VREG_W-2:0] = vsm_shift_q[VREG_W-1:1];
        end
    end

    // gather shift register assignment
    assign elem_tmp_d    = vs1_tmp_q;
    assign mask_tmp_d    = vsm_shift_q[0];
    assign redinit_tmp_d = vsm_shift_q[31:0];
    always_comb begin
        gather_shift_d = vreg_rd_q;
        v0msk_shift_d  = vreg_mask_i;
        if (~state_gather_q.gather_fetch) begin
            gather_shift_d[VREG_W-GATHER_OP_W-1:0] = gather_shift_q[VREG_W-1:GATHER_OP_W];
        end
        if (~state_gather_q.first_cycle) begin
            if (result_valid_d) begin
                v0msk_shift_d[VREG_W-2:0] = v0msk_shift_q[VREG_W-1:1];
            end else begin
                v0msk_shift_d             = v0msk_shift_q;
            end
        end
    end

    assign elem_d    = elem_tmp_q;
    assign mask_d    = mask_tmp_q;
    assign redinit_d = redinit_tmp_q;
    always_comb begin
        elem_idx_valid_d = COMB_INIT_ZERO ? '0 : 'x;
        unique case (state_gather_q.emul)
            EMUL_1: elem_idx_valid_d = elem_tmp_q[31:$clog2(VREG_W/8)  ] == '0;
            EMUL_2: elem_idx_valid_d = elem_tmp_q[31:$clog2(VREG_W/8)+1] == '0;
            EMUL_4: elem_idx_valid_d = elem_tmp_q[31:$clog2(VREG_W/8)+2] == '0;
            EMUL_8: elem_idx_valid_d = elem_tmp_q[31:$clog2(VREG_W/8)+3] == '0;
        endcase
    end

    // result shift register assignment:
    always_comb begin
        vd_shift_d    = vd_shift_q;
        vdmsk_shift_d = vdmsk_shift_q;
        if (result_valid_q) begin
            //vd_shift_d    = COMB_INIT_ZERO ? '0 : 'x;
            //vdmsk_shift_d = COMB_INIT_ZERO ? '0 : 'x;
            case (state_res_q.eew)
                VSEW_8: begin
                    vd_shift_d    = {   result_q[7 :0] , vd_shift_q   [VREG_W-1:8 ]};
                    vdmsk_shift_d = {   result_mask_q  , vdmsk_shift_q[VMSK_W-1:1 ]};
                end
                VSEW_16: begin
                    vd_shift_d    = {   result_q[15:0] , vd_shift_q   [VREG_W-1:16]};
                    vdmsk_shift_d = {{2{result_mask_q}}, vdmsk_shift_q[VMSK_W-1:2 ]};
                end
                VSEW_32: begin
                    vd_shift_d    = {   result_q       , vd_shift_q   [VREG_W-1:32]};
                    vdmsk_shift_d = {{4{result_mask_q}}, vdmsk_shift_q[VMSK_W-1:4 ]};
                end
            endcase
        end
    end

    // XREG write-back
    assign xreg_valid_o = state_res_q.busy & state_res_q.mode.xreg & ((state_res_q.mode.op == ELEM_XMV) ? state_res_q.first_cycle : state_res_q.last_cycle);
    assign xreg_o       = result_q;

    //
    always_comb begin
        first_valid_result_d = first_valid_result_q;
        if (result_valid_q) begin
            first_valid_result_d = 1'b0;
        end
        if (~state_res_q.busy | (state_res_q.last_cycle & ~state_res_q.requires_flush)) begin
            first_valid_result_d = 1'b1;
        end
    end
    always_comb begin
        count_store_d.val = COMB_INIT_ZERO ? '0 : 'x;
        case (state_res_q.eew)
            VSEW_8:  count_store_d.val = state_vd_q.count_store.val + {{(ELEM_COUNTER_W-1){1'b0}}, result_valid_q      };
            VSEW_16: count_store_d.val = state_vd_q.count_store.val + {{(ELEM_COUNTER_W-2){1'b0}}, result_valid_q, 1'b0};
            VSEW_32: count_store_d.val = state_vd_q.count_store.val + {{(ELEM_COUNTER_W-3){1'b0}}, result_valid_q, 2'b0};
        endcase
        if (state_res_q.first_cycle | first_valid_result_q) begin
            count_store_d.val      = '0;
            count_store_d.val[1:0] = COMB_INIT_ZERO ? '0 : 'x;
            case (state_res_q.eew)
                VSEW_8:  count_store_d.val[1:0] = 2'b00;
                VSEW_16: count_store_d.val[1:0] = 2'b01;
                VSEW_32: count_store_d.val[1:0] = 2'b11;
            endcase
        end
    end
    assign vd_store_d = ~state_res_q.mode.xreg & (count_store_d.part.low == '1);

    //
    assign vreg_wr_en_d   = state_vd_q.busy & state_vd_q.vd_store;
    assign vreg_wr_addr_d = state_vd_q.vd | {2'b0, state_vd_q.count_store.part.mul[2:0]};
    assign vreg_wr_mask_d = vreg_wr_en_o ? vdmsk_shift_q : '0;
    assign vreg_wr_d      = vd_shift_q;
    assign vreg_wr_last_d = state_vd_q.busy & state_vd_q.last_cycle & ~state_vd_q.requires_flush;
    assign vreg_wr_base_d = state_vd_q.vd;
    assign vreg_wr_emul_d = state_vd_q.emul;


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
        counter_inc    = COMB_INIT_ZERO ? '0 : 'x;
        result_d       = COMB_INIT_ZERO ? '0 : 'x;
        result_mask_d  = COMB_INIT_ZERO ? '0 : 'x;
        result_valid_d = COMB_INIT_ZERO ? '0 : 'x;
        unique case (state_ex_q.mode.op)
            // move from vreg index 0 to xreg with sign extension
            ELEM_XMV: begin
                unique case (state_ex_q.eew)
                    VSEW_8:  result_d = {{24{elem_q[7 ]}}, elem_q[7 :0]};
                    VSEW_16: result_d = {{16{elem_q[15]}}, elem_q[15:0]};
                    VSEW_32: result_d =                    elem_q       ;
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
                if (state_ex_q.count_gather == elem_q[$clog2(VREG_W/8)-1:$clog2(GATHER_OP_W/8)]) begin
                    result_d       = gather_shift_q[(elem_q[$clog2(GATHER_OP_W/8)-1:0] & ({$clog2(GATHER_OP_W/8){1'b1}} << 2)) * 8 +: 32];
                    result_d[15:0] = gather_shift_q[(elem_q[$clog2(GATHER_OP_W/8)-1:0] & ({$clog2(GATHER_OP_W/8){1'b1}} << 1)) * 8 +: 16];
                    result_d[7 :0] = gather_shift_q[(elem_q[$clog2(GATHER_OP_W/8)-1:0] & ({$clog2(GATHER_OP_W/8){1'b1}}     )) * 8 +: 8 ];
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
                    endcase
                end
                result_mask_d  = ~state_ex_q.vl_0;
                result_valid_d = state_ex_q.last_cycle;
            end

        endcase
    end

endmodule
