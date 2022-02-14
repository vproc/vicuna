// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_sld #(
        parameter int unsigned        VREG_W          = 128,  // width in bits of vector registers
        parameter int unsigned        VMSK_W          = 16,   // width of vector register masks (= VREG_W / 8)
        parameter int unsigned        CFG_VL_W        = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned        SLD_OP_W        = 64,   // SLD unit operand width in bits
        parameter int unsigned        XIF_ID_W        = 3,    // width in bits of instruction IDs
        parameter int unsigned        XIF_ID_CNT      = 8,    // total count of instruction IDs
        parameter int unsigned        MAX_WR_ATTEMPTS = 1,    // max required vregfile write attempts
        parameter bit                 BUF_VREG        = 1'b1, // insert pipeline stage after vreg read
        parameter bit                 BUF_OPERANDS    = 1'b1, // insert pipeline stage after operand extraction
        parameter bit                 BUF_RESULTS     = 1'b1, // insert pipeline stage after computing result
        parameter bit                 DONT_CARE_ZERO  = 1'b0  // initialize don't care values to zero
    )(
        input  logic                  clk_i,
        input  logic                  async_rst_ni,
        input  logic                  sync_rst_ni,

        input  logic [XIF_ID_W-1:0]   id_i,
        input  vproc_pkg::cfg_vsew    vsew_i,
        input  vproc_pkg::cfg_emul    emul_i,
        input  logic [CFG_VL_W-1:0]   vl_i,
        input  logic                  vl_0_i,

        input  logic                  op_rdy_i,
        output logic                  op_ack_o,

        input  vproc_pkg::op_mode_sld mode_i,
        input  vproc_pkg::op_regs     rs1_i,
        input  vproc_pkg::op_regs     rs2_i,
        input  logic [4:0]            vd_i,

        input  logic [31:0]           vreg_pend_wr_i,
        output logic [31:0]           vreg_pend_rd_o,
        input  logic [31:0]           vreg_pend_rd_i,

        output logic [31:0]           clear_wr_hazards_o,

        input  logic [XIF_ID_CNT-1:0] instr_spec_i,
        input  logic [XIF_ID_CNT-1:0] instr_killed_i,
        output logic                  instr_done_valid_o,
        output logic [XIF_ID_W-1:0]   instr_done_id_o,

        // connections to register file:
        input  logic [VREG_W-1:0]     vreg_mask_i,
        input  logic [VREG_W-1:0]     vreg_rd_i,
        output logic [4:0]            vreg_rd_addr_o,
        output logic [VREG_W-1:0]     vreg_wr_o,
        output logic [4:0]            vreg_wr_addr_o,
        output logic [VMSK_W-1:0]     vreg_wr_mask_o,
        output logic                  vreg_wr_en_o
    );

    import vproc_pkg::*;

    if ((SLD_OP_W & (SLD_OP_W - 1)) != 0 || SLD_OP_W < 32 || SLD_OP_W >= VREG_W) begin
        $fatal(1, "The vector SLD operand width SLD_OP_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", SLD_OP_W);
    end

    if (MAX_WR_ATTEMPTS < 1 || (1 << (MAX_WR_ATTEMPTS - 1)) > VREG_W / SLD_OP_W) begin
        $fatal(1, "The maximum number of write attempts MAX_WR_ATTEMPTS of a unit ",
                  "must be at least 1 and 2^(MAX_WR_ATTEMPTS-1) must be less than or ",
                  "equal to the ratio of the vector register width vs the operand width ",
                  "of that unit.  ",
                  "For the vector SLD unit MAX_WR_ATTEMPTS is %d and that ratio is %d.",
                  MAX_WR_ATTEMPTS, VREG_W / SLD_OP_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (MAX_WR_ATTEMPTS - 1)) - 1;


    ///////////////////////////////////////////////////////////////////////////
    // SLD UNIT STATE:

    localparam int unsigned SLD_CYCLES_PER_VREG = VREG_W / SLD_OP_W;
    localparam int unsigned SLD_COUNTER_W       = $clog2(SLD_CYCLES_PER_VREG) + 4;

    localparam int unsigned SLD_OP_SHFT_W = $clog2(SLD_OP_W / 8);

    localparam int unsigned RESMSK_W = SLD_OP_W / 8; // size of result masks

    // note that in contrast to other units the mul part of the counter is 4 bits
    typedef union packed {
        logic [SLD_COUNTER_W-1:0] val;
        struct packed {
            logic [3:0]               mul; // mul part (vreg index)
            logic [SLD_COUNTER_W-5:0] low; // counter part in vreg (vreg pos)
        } part;
    } sld_counter;

    typedef struct packed {
        sld_counter          count;
        logic                first_cycle;
        logic                last_cycle;
        logic [XIF_ID_W-1:0] id;
        op_mode_sld          mode;
        cfg_vsew             eew;        // effective element width
        cfg_emul             emul;       // effective MUL factor
        logic [CFG_VL_W-1:0] vl;
        logic                vl_0;
        op_regs              rs1;
        op_regs              rs2;
        logic                vs2_fetch;
        logic                v0msk_fetch;
        logic                v0msk_shift;
        logic [4:0]          vd;
        logic                vd_store;
    } sld_state;

    logic        state_valid_q,  state_valid_d;
    sld_state    state_q,        state_d;
    logic [31:0] vreg_pend_wr_q, vreg_pend_wr_d; // local copy of global vreg write mask
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_state_valid
        if (~async_rst_ni) begin
            state_valid_q <= 1'b0;
        end
        else if (~sync_rst_ni) begin
            state_valid_q <= 1'b0;
        end else begin
            state_valid_q <= state_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_sld_state
        state_q        <= state_d;
        vreg_pend_wr_q <= vreg_pend_wr_d;
    end

    // in contrast to other units the last cycle is delayed by the cycles required for one VREG
    logic last_cycle;
    always_comb begin
        last_cycle = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (state_q.emul)
            EMUL_1: last_cycle = ~state_q.count.part.mul[3] &                                        state_q.count.part.low == '1;
            EMUL_2: last_cycle = ~state_q.count.part.mul[3] & (state_q.count.part.mul[  0] == '1) & (state_q.count.part.low == '1);
            EMUL_4: last_cycle = ~state_q.count.part.mul[3] & (state_q.count.part.mul[1:0] == '1) & (state_q.count.part.low == '1);
            EMUL_8: last_cycle = ~state_q.count.part.mul[3] & (state_q.count.part.mul[2:0] == '1) & (state_q.count.part.low == '1);
            default: ;
        endcase
    end

    sld_counter slide_count;
    always_comb begin
        slide_count.val = state_q.rs1.r.xval[SLD_OP_SHFT_W +: SLD_COUNTER_W];
        if (state_q.mode.slide1) begin
            if (state_q.mode.dir == SLD_UP) begin
                // slide_count is all zeroes for up slide, except for a byte slide of 4 when the
                // operand width is 32 bits, then it is 1 (right shift by log2(SLD_OP_W/8) = 2 bits)
                unique case (state_q.eew)
                    VSEW_8,
                    VSEW_16: slide_count.val = '0;
                    VSEW_32: slide_count.val = {{SLD_COUNTER_W-1{1'b0}}, SLD_OP_W == 32};
                    default: ;
                endcase
            end else begin
                // slide_count is all ones for down slide, even with a byte slide value of -4
                slide_count.val = '1;
            end
        end
    end

    logic slide_fetch;
    always_comb begin
        slide_fetch = 1'b0;
        if (state_q.count.part.low == slide_count.part.low) begin
            unique case (state_q.emul)
                EMUL_1: begin
                    slide_fetch =   state_q.count.part.mul - slide_count.part.mul             == '0;
                end
                EMUL_2: begin
                    slide_fetch = ((state_q.count.part.mul - slide_count.part.mul) & 4'b1110) == '0;
                end
                EMUL_4: begin
                    slide_fetch = ((state_q.count.part.mul - slide_count.part.mul) & 4'b1100) == '0;
                end
                EMUL_8: begin
                    slide_fetch = ((state_q.count.part.mul - slide_count.part.mul) & 4'b1000) == '0;
                end
                default: ;
            endcase
        end
    end

    logic pipeline_ready;
    always_comb begin
        op_ack_o       = 1'b0;
        state_valid_d  = state_valid_q;
        state_d        = state_q;
        vreg_pend_wr_d = vreg_pend_wr_q & vreg_pend_wr_i;

        if (((~state_valid_q) | (last_cycle & pipeline_ready)) & op_rdy_i) begin
            op_ack_o            = 1'b1;
            state_d.count.val   = '0;
            if (mode_i.dir == SLD_DOWN) begin
                state_d.count.part.mul = '1;
            end
            state_valid_d       = 1'b1;
            state_d.first_cycle = 1'b1;
            state_d.id          = id_i;
            state_d.mode        = mode_i;
            state_d.eew         = vsew_i;
            state_d.emul        = emul_i;
            state_d.vl          = vl_i;
            state_d.vl_0        = vl_0_i;
            state_d.rs1         = rs1_i;
            if (~mode_i.slide1) begin
                // convert element offset to byte offset for the relevant section of rs1 and negate
                // for down slides
                if (mode_i.dir == SLD_UP) begin
                    unique case (vsew_i)
                        VSEW_8:  state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+2:0]      };
                        VSEW_16: state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                        VSEW_32: state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                        default: ;
                    endcase
                end else begin
                    unique case (vsew_i)
                        VSEW_8:  state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+2:0]      };
                        VSEW_16: state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                        VSEW_32: state_d.rs1.r.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, rs1_i.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                        default: ;
                    endcase
                end
            end
            state_d.rs2         = rs2_i;
            state_d.rs2.vreg    = 1'b0; // use vreg bit as valid signal
            state_d.v0msk_fetch = mode_i.dir == SLD_UP;
            state_d.v0msk_shift = 1'b0;
            state_d.vd          = vd_i;
            state_d.vd_store    = 1'b0;
            vreg_pend_wr_d      = vreg_pend_wr_i;
        end
        else if (state_valid_q & pipeline_ready) begin
            state_d.count.val   = state_q.count.val + 1;
            state_valid_d       = ~last_cycle;
            state_d.first_cycle = 1'b0;
            state_d.v0msk_fetch = 1'b0;
            state_d.v0msk_shift = 1'b0;
            state_d.vd_store    = 1'b0;
            if (state_q.count.part.low == '1) begin
                state_d.v0msk_fetch = state_q.count.part.mul[3];
                state_d.v0msk_shift = 1'b1;
                if (~state_q.count.part.mul[3]) begin
                    state_d.vd[2:0] = state_q.vd[2:0] + 3'b1;
                end
            end
            if (state_q.count.part.low == slide_count.part.low) begin
                state_d.rs2.vreg = slide_fetch; // set vs2 valid bit after fetch
            end
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // SLD PIPELINE BUFFERS:

    // pass state information along pipeline:
    logic                       state_ex_ready,                     state_res_ready,   state_vd_ready;
    logic     state_init_stall,                                                        state_vd_stall;
    logic     state_init_valid, state_ex_valid_q, state_ex_valid_d, state_res_valid_q, state_vd_valid_q;
    sld_state state_init,       state_ex_q,       state_ex_d,       state_res_q,       state_vd_q;
    always_comb begin
        state_init_valid            = state_valid_q;
        state_init                  = state_q;
        state_init.last_cycle       = state_valid_q & last_cycle;
        unique case (state_q.emul)
            EMUL_2: state_init.rs2.r.vaddr[0:0] = state_q.count.part.mul[0:0] - slide_count.part.mul[0:0];
            EMUL_4: state_init.rs2.r.vaddr[1:0] = state_q.count.part.mul[1:0] - slide_count.part.mul[1:0];
            EMUL_8: state_init.rs2.r.vaddr[2:0] = state_q.count.part.mul[2:0] - slide_count.part.mul[2:0];
            default: ;
        endcase

        // TODO rs2.vreg does not need to be cleared since vslide1down has to use vl anyways
        state_init.rs2.vreg = slide_fetch | state_q.rs2.vreg;   // TODO use only this
        //state_init.rs2.vreg = (state_q.count.part.low == slide_count.part.low) ? slide_fetch : state_q.rs2.vreg; // TODO remove this

        state_init.vs2_fetch = slide_fetch;
        state_init.vd_store  = ~state_q.count.part.mul[3] & state_q.count.part.low == '1;
    end
    logic unpack_ready;
    assign pipeline_ready = unpack_ready & ~state_init_stall;

    // operands and result:
    logic [SLD_OP_W/8-1:0] v0msk_q,        v0msk_d;
    logic                  operand_low_valid_q, operand_low_valid_d;
    logic [SLD_OP_W  -1:0] operand_low_q,  operand_low_d;
    logic [SLD_OP_W  -1:0] operand_high_q, operand_high_d;
    logic [SLD_OP_W  -1:0] result_q,       result_d;
    logic [RESMSK_W  -1:0] result_mask_q,  result_mask_d;
    logic [SLD_OP_W/8-1:0] write_mask_q,   write_mask_d;

    // result shift register:
    logic [VREG_W-1:0] vd_shift_q,     vd_shift_d;
    logic [VMSK_W-1:0] vdmsk_shift_q,  vdmsk_shift_d;

    // vreg write buffers
    localparam WRITE_BUFFER_SZ = (MAX_WR_DELAY > 0) ? MAX_WR_DELAY : 1;
    logic              vreg_wr_en_q   [WRITE_BUFFER_SZ], vreg_wr_en_d;
    logic [4:0]        vreg_wr_addr_q [WRITE_BUFFER_SZ], vreg_wr_addr_d;
    logic [VMSK_W-1:0] vreg_wr_mask_q [WRITE_BUFFER_SZ], vreg_wr_mask_d;
    logic [VREG_W-1:0] vreg_wr_q      [WRITE_BUFFER_SZ], vreg_wr_d;
    logic              vreg_wr_clear_q[WRITE_BUFFER_SZ], vreg_wr_clear_d;

    // hazard clear registers
    logic [31:0] clear_wr_hazards_q, clear_wr_hazards_d;

    generate
        if (BUF_OPERANDS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_stage_ex_valid
                if (~async_rst_ni) begin
                    state_ex_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_ex_valid_q <= 1'b0;
                end
                else if (state_ex_ready) begin
                    state_ex_valid_q <= state_ex_valid_d;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_sld_stage_ex
                if (state_ex_ready & state_ex_valid_d) begin
                    state_ex_q     <= state_ex_d;
                    operand_high_q <= operand_high_d;
                    v0msk_q        <= v0msk_d;
                end
            end
            assign state_ex_ready = ~state_ex_valid_q | state_res_ready;
        end else begin
            always_comb begin
                state_ex_valid_q = state_ex_valid_d;
                state_ex_q       = state_ex_d;
                operand_high_q   = operand_high_d;
                v0msk_q          = v0msk_d;
            end
            assign state_ex_ready = state_res_ready;
        end
        // low operand is always buffered
        always_ff @(posedge clk_i) begin
            if (state_ex_ready & state_ex_valid_d) begin
                operand_low_valid_q <= operand_low_valid_d;
                operand_low_q       <= operand_low_d;
            end
        end

        if (BUF_RESULTS) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_stage_res_valid
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
            always_ff @(posedge clk_i) begin : vproc_sld_stage_res
                if (state_res_ready & state_ex_valid_q) begin
                    state_res_q   <= state_ex_q;
                    result_q      <= result_d;
                    result_mask_q <= result_mask_d;
                    write_mask_q  <= write_mask_d;
                end
            end
            assign state_res_ready = ~state_res_valid_q | state_vd_ready;
        end else begin
            always_comb begin
                state_res_valid_q = state_ex_valid_q;
                state_res_q       = state_ex_q;
                result_q          = result_d;
                result_mask_q     = result_mask_d;
                write_mask_q      = write_mask_d;
            end
            assign state_res_ready = state_vd_ready;
        end

        always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_sld_stage_vd_valid
            if (~async_rst_ni) begin
                state_vd_valid_q <= 1'b0;
            end
            else if (~sync_rst_ni) begin
                state_vd_valid_q <= 1'b0;
            end
            else if (state_vd_ready) begin
                state_vd_valid_q <= state_res_valid_q;
            end
        end
        always_ff @(posedge clk_i) begin : vproc_sld_stage_vd
            if (state_vd_ready & state_res_valid_q) begin
                state_vd_q     <= state_res_q;
                vd_shift_q     <= vd_shift_d;
                vdmsk_shift_q  <= vdmsk_shift_d;
            end
        end
        assign state_vd_ready = ~state_vd_valid_q | ~state_vd_stall;

        if (MAX_WR_DELAY > 0) begin
            always_ff @(posedge clk_i) begin : vproc_sld_wr_delay
                vreg_wr_en_q   [0] <= vreg_wr_en_d;
                vreg_wr_addr_q [0] <= vreg_wr_addr_d;
                vreg_wr_mask_q [0] <= vreg_wr_mask_d;
                vreg_wr_q      [0] <= vreg_wr_d;
                vreg_wr_clear_q[0] <= vreg_wr_clear_d;
                for (int i = 1; i < MAX_WR_DELAY; i++) begin
                    vreg_wr_en_q   [i] <= vreg_wr_en_q   [i-1];
                    vreg_wr_addr_q [i] <= vreg_wr_addr_q [i-1];
                    vreg_wr_mask_q [i] <= vreg_wr_mask_q [i-1];
                    vreg_wr_q      [i] <= vreg_wr_q      [i-1];
                    vreg_wr_clear_q[i] <= vreg_wr_clear_q[i-1];
                end
            end
        end

        always_ff @(posedge clk_i) begin
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
    // write hazard clearing
    always_comb begin
        clear_wr_hazards_d     = vreg_wr_clear_d                 ? (32'b1 << vreg_wr_addr_d                ) : 32'b0;
        if (MAX_WR_DELAY > 0) begin
            clear_wr_hazards_d = vreg_wr_clear_q[MAX_WR_DELAY-1] ? (32'b1 << vreg_wr_addr_q[MAX_WR_DELAY-1]) : 32'b0;
        end
    end
    assign clear_wr_hazards_o = clear_wr_hazards_q;

    // Stall vreg reads until pending writes are complete; note that vreg read
    // stalling always happens in the init stage, since otherwise a substantial
    // amount of state would have to be forwarded (such as vreg_pend_wr_q)
    assign state_init_stall = (state_init.vs2_fetch   & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                              (state_init.v0msk_fetch & state_init.mode.masked & vreg_pend_wr_q[0]);

    // Stall vreg writes until pending reads of the destination register are
    // complete and while the instruction is speculative
    assign state_vd_stall = state_vd_q.vd_store & (vreg_pend_rd_i[state_vd_q.vd] | instr_spec_i[state_vd_q.id]);

    assign instr_done_valid_o = state_vd_valid_q & state_vd_q.last_cycle & ~state_vd_stall;
    assign instr_done_id_o    = state_vd_q.id;

    // pending vreg reads
    // Note: The pipeline might stall while reading a vreg, hence a vreg has to
    // be part of the pending reads until the read is complete.
    logic [31:0] pend_vs2;
    always_comb begin
        pend_vs2 = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_q.emul)
            EMUL_1: pend_vs2 = 32'h01 <<  state_q.rs2.r.vaddr;
            EMUL_2: pend_vs2 = 32'h03 << {state_q.rs2.r.vaddr[4:1], 1'b0};
            EMUL_4: pend_vs2 = 32'h0F << {state_q.rs2.r.vaddr[4:2], 2'b0};
            EMUL_8: pend_vs2 = 32'hFF << {state_q.rs2.r.vaddr[4:3], 3'b0};
            default: ;
        endcase
    end
    // Note: the v0 mask has no extra buffer and is always read in state_vreg
    logic [31:0] unpack_pend_rd;
    assign vreg_pend_rd_o = ((
            ( state_init_valid                                                            ? pend_vs2                        : '0) |
            ((state_init_valid & (state_init.count.part.mul[3] | state_init.v0msk_fetch)) ? {31'b0, state_init.mode.masked} : '0)
        ) & ~vreg_pend_wr_q) |
    unpack_pend_rd;

    logic [3:0] debug_count_part_mul_3;
    logic debug_v0msk_fetch, debug_cond;
    logic [4:0] debug_vs2_addr, debug_vs2_fetch_addr;
    assign debug_v0msk_fetch      = state_init.v0msk_fetch;
    assign debug_count_part_mul_3 = state_init.count.part.mul;
    assign debug_cond = state_init_valid & (state_init.count.part.mul[3] | state_init.v0msk_fetch);
    assign debug_vs2_addr = state_q.rs2.r.vaddr;
    assign debug_vs2_fetch_addr = state_init.rs2.r.vaddr;


    ///////////////////////////////////////////////////////////////////////////
    // SLD REGISTER READ/WRITE:

    unpack_flags [1:0]       unpack_op_flags;
    logic        [1:0][4 :0] unpack_op_vaddr;
    logic        [1:0][31:0] unpack_op_xval;
    always_comb begin
        unpack_op_flags  [0]          = unpack_flags'('0);
        unpack_op_flags  [0].shift    = 1'b1;
        unpack_op_flags  [0].load     = state_init.vs2_fetch;
        unpack_op_flags  [0].elemwise = '0;
        unpack_op_vaddr  [0]          = state_init.rs2.r.vaddr;
        unpack_op_xval   [0]          = '0;
        unpack_op_flags  [1]          = unpack_flags'('0);
        unpack_op_flags  [1].shift    = state_init.v0msk_shift;
        unpack_op_flags  [1].load     = state_init.v0msk_fetch & state_init.mode.masked;
        unpack_op_flags  [1].elemwise = '0;
        unpack_op_vaddr  [1]          = '0;
        unpack_op_xval   [1]          = '0;
    end

    localparam int unsigned UNPACK_VPORT_W [2] = '{VREG_W,VREG_W};
    localparam int unsigned UNPACK_VADDR_W [2] = '{5,5};
    localparam int unsigned UNPACK_OP_W    [2] = '{SLD_OP_W,SLD_OP_W/8};
    localparam int unsigned UNPACK_OP_STAGE[2] = '{1,1};
    localparam int unsigned UNPACK_OP_SRC  [2] = '{0,1};

    logic                     unpack_valid;
    sld_state                 unpack_state;
    logic [1:0][SLD_OP_W-1:0] unpack_ops;
    logic [1:0][4:0]          unpack_vreg_addr;
    logic [1:0][VREG_W-1:0]   unpack_vreg_data;
    vproc_vregunpack #(
        .MAX_VPORT_W          ( VREG_W                               ),
        .MAX_VADDR_W          ( 5                                    ),
        .VPORT_CNT            ( 2                                    ),
        .VPORT_W              ( UNPACK_VPORT_W                       ),
        .VADDR_W              ( UNPACK_VADDR_W                       ),
        .VPORT_ADDR_ZERO      ( 2'b10                                ),
        .VPORT_BUFFER         ( 2'b01                                ),
        .MAX_OP_W             ( SLD_OP_W                             ),
        .OP_CNT               ( 2                                    ),
        .OP_W                 ( UNPACK_OP_W                          ),
        .OP_STAGE             ( UNPACK_OP_STAGE                      ),
        .OP_SRC               ( UNPACK_OP_SRC                        ),
        .OP_ADDR_OFFSET_OP0   ( 2'b00                                ),
        .OP_MASK              ( 2'b10                                ),
        .OP_XREG              ( 2'b00                                ),
        .OP_NARROW            ( 2'b00                                ),
        .OP_ALLOW_ELEMWISE    ( 2'b00                                ),
        .OP_ALWAYS_ELEMWISE   ( 2'b00                                ),
        .OP_HOLD_FLAG         ( 2'b00                                ),
        .UNPACK_STAGES        ( 2                                    ),
        .FLAGS_T              ( unpack_flags                         ),
        .CTRL_DATA_W          ( $bits(sld_state)                     ),
        .DONT_CARE_ZERO       ( DONT_CARE_ZERO                       )
    ) sld_unpack (
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
        .pipe_out_valid_o     ( unpack_valid                         ),
        .pipe_out_ready_i     ( state_ex_ready                       ),
        .pipe_out_ctrl_o      ( unpack_state                         ),
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
    logic [SLD_OP_W-1:0] operand;
    assign operand = unpack_ops[0];
    assign v0msk_d = unpack_ops[1][SLD_OP_W/8-1:0];

    assign state_ex_valid_d = unpack_valid;
    always_comb begin
        state_ex_d = unpack_state;
        // overwrite rs1 with slide amount
        if (unpack_state.mode.slide1) begin
            if (unpack_state.mode.dir == SLD_UP) begin
                unique case (unpack_state.eew)
                    VSEW_8:  state_ex_d.rs1.r.xval[SLD_OP_SHFT_W-1:0] = {{SLD_OP_SHFT_W-3{1'b0}}, 3'b001};
                    VSEW_16: state_ex_d.rs1.r.xval[SLD_OP_SHFT_W-1:0] = {{SLD_OP_SHFT_W-3{1'b0}}, 3'b010};
                    VSEW_32: state_ex_d.rs1.r.xval[SLD_OP_SHFT_W-1:0] = {{SLD_OP_SHFT_W-3{1'b0}}, 3'b100};
                    default: ;
                endcase
            end else begin
                unique case (unpack_state.eew)
                    VSEW_8:  state_ex_d.rs1.r.xval[SLD_OP_SHFT_W-1:0] = {{SLD_OP_SHFT_W-3{1'b1}}, 3'b111};
                    VSEW_16: state_ex_d.rs1.r.xval[SLD_OP_SHFT_W-1:0] = {{SLD_OP_SHFT_W-3{1'b1}}, 3'b110};
                    VSEW_32: state_ex_d.rs1.r.xval[SLD_OP_SHFT_W-1:0] = {{SLD_OP_SHFT_W-3{1'b1}}, 3'b100};
                    default: ;
                endcase
            end
        end
    end

    // extract operands, substitute with rs1 when invalid to accomodate 1up and 1down operations
    logic [SLD_COUNTER_W-1:0] vl_cnt;
    assign vl_cnt = {1'b0, unpack_state.vl[CFG_VL_W-1:CFG_VL_W-SLD_COUNTER_W+1]} + 1;
    always_comb begin
        operand_high_d      = operand;
        operand_low_d       = DONT_CARE_ZERO ? '0 : 'x;
        operand_low_valid_d = 1'b0;
        if ((unpack_state.mode.dir == SLD_DOWN) & unpack_state.mode.slide1 & (unpack_state.count.val[SLD_COUNTER_W-2:0] == unpack_state.vl[CFG_VL_W-1:$clog2(SLD_OP_W/8)])) begin
            operand_high_d[31:0] = unpack_state.rs1.r.xval;
        end
        unique case (unpack_state.eew)
            VSEW_8: begin
                for (int i = 0; i < SLD_OP_W / 8 ; i++) begin
                    operand_low_d[i*8  +: 8 ] = unpack_state.rs1.r.xval[7 :0];
                end
            end
            VSEW_16: begin
                for (int i = 0; i < SLD_OP_W / 16; i++) begin
                    operand_low_d[i*16 +: 16] = unpack_state.rs1.r.xval[15:0];
                end
            end
            VSEW_32: begin
                for (int i = 0; i < SLD_OP_W / 32; i++) begin
                    operand_low_d[i*32 +: 32] = unpack_state.rs1.r.xval;
                end
            end
            default: ;
        endcase
        if (~unpack_state.first_cycle & state_ex_q.rs2.vreg) begin
            operand_low_valid_d = 1'b1;
            for (int i = 0; i < SLD_OP_W / 8; i++) begin
                if (~unpack_state.mode.slide1 | (unpack_state.count.val[SLD_COUNTER_W-2:0] != unpack_state.vl[CFG_VL_W-1:$clog2(SLD_OP_W/8)]) | (i <= unpack_state.vl[$clog2(SLD_OP_W/8)-1:0])) begin
                    operand_low_d[i*8 +: 8] = operand_high_q[i*8 +: 8];
                end
            end
        end
    end
    assign write_mask_d = v0msk_q;

    logic [VREG_W    -1:0] vl_mask;
    logic [SLD_OP_W/8-1:0] result_vl_mask;
    assign vl_mask        = state_res_q.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_res_q.vl));
    assign result_vl_mask = vl_mask[state_res_q.count.val[SLD_COUNTER_W-2:0]*SLD_OP_W/8 +: SLD_OP_W/8];

    // result shift register assignment:
    assign vd_shift_d    = {result_q, vd_shift_q[VREG_W-1:SLD_OP_W]};
    assign vdmsk_shift_d = {result_mask_q & result_vl_mask & (state_res_q.mode.masked ? write_mask_q : {SLD_OP_W/8{1'b1}}), vdmsk_shift_q[VMSK_W-1:RESMSK_W]};

    //
    assign vreg_wr_en_d    = state_vd_valid_q & state_vd_q.vd_store & ~state_vd_stall & ~instr_killed_i[state_vd_q.id];
    assign vreg_wr_addr_d  = state_vd_q.vd;
    assign vreg_wr_mask_d  = vreg_wr_en_o ? vdmsk_shift_q : '0;
    assign vreg_wr_d       = vd_shift_q;
    assign vreg_wr_clear_d = state_vd_valid_q & state_vd_q.vd_store & ~state_vd_stall;


    ///////////////////////////////////////////////////////////////////////////
    // SLIDING OPERATION:

    logic [SLD_OP_SHFT_W-1:0] slide_bytes;
    assign slide_bytes = state_ex_q.rs1.r.xval[SLD_OP_SHFT_W-1:0];

    always_comb begin
        result_d      = DONT_CARE_ZERO ? '0 : 'x;
        result_mask_d = DONT_CARE_ZERO ? '0 : 'x;

        for (int i = 0; i < SLD_OP_W/8; i++) begin
            if ($clog2(SLD_OP_W/8)'(i) < slide_bytes) begin
                result_d     [i*8 +: 8] = operand_low_q [($clog2(SLD_OP_W)'(SLD_OP_W/8 + i) - {3'b000, slide_bytes}) * 8 +: 8];
                result_mask_d[i]        = operand_low_valid_q;
            end else begin
                result_d     [i*8 +: 8] = operand_high_q[($clog2(SLD_OP_W)'(             i) - {3'b000, slide_bytes}) * 8 +: 8];
                result_mask_d[i]        = state_ex_q.rs2.vreg;
            end
        end

        if (state_ex_q.mode.slide1) begin
            result_mask_d = {RESMSK_W{1'b1}};
        end
    end


`ifdef VPROC_SVA
`include "vproc_sld_sva.svh"
`endif

endmodule
