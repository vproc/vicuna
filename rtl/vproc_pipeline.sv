// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_pipeline import vproc_pkg::*; #(
        parameter int unsigned          VREG_W              = 128,  // width in bits of vector registers
        parameter int unsigned          CFG_VL_W            = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned          XIF_ID_W            = 3,    // width in bits of instruction IDs
        parameter int unsigned          XIF_ID_CNT          = 8,    // total count of instruction IDs
        parameter bit [UNIT_CNT-1:0]    UNITS               = '0,
        parameter int unsigned          MAX_VPORT_W         = 128,  // max port width
        parameter int unsigned          MAX_VADDR_W         = 5,    // max addr width
        parameter int unsigned          VPORT_CNT           = 1,
        parameter int unsigned          VPORT_W [VPORT_CNT] = '{0},
        parameter int unsigned          VADDR_W [VPORT_CNT] = '{0},
        parameter bit [VPORT_CNT-1:0]   VPORT_BUFFER        = '0,   // buffer port
        parameter int unsigned          MAX_OP_W            = 64,
        parameter int unsigned          OP_CNT              = 1,
        parameter int unsigned          OP_W    [OP_CNT   ] = '{0}, // op widths
        parameter int unsigned          OP_STAGE[OP_CNT   ] = '{0}, // op load stage
        parameter int unsigned          OP_SRC  [OP_CNT   ] = '{0}, // op port index
        parameter int unsigned          OP_DYN_ADDR_SRC     = 0,    // dyn addr src idx
        parameter bit [OP_CNT-1:0]      OP_DYN_ADDR         = '0,   // dynamic addr
        parameter bit [OP_CNT-1:0]      OP_MASK             = '0,   // op is a mask
        parameter bit [OP_CNT-1:0]      OP_XREG             = '0,   // op may be XREG
        parameter bit [OP_CNT-1:0]      OP_NARROW           = '0,   // op may be narrow
        parameter bit [OP_CNT-1:0]      OP_ALLOW_ELEMWISE   = '0,   // op may be 1 elem
        parameter bit [OP_CNT-1:0]      OP_ALWAYS_ELEMWISE  = '0,   // op is 1 elem
        parameter bit [OP_CNT-1:0]      OP_ALT_COUNTER      = '0,
        parameter bit [OP_CNT-1:0]      OP_ALWAYS_VREG      = '0,
        parameter int unsigned          UNPACK_STAGES       = 0,
        parameter int unsigned          MAX_RES_W           = 64,
        parameter int unsigned          RES_CNT             = 1,
        parameter int unsigned          RES_W   [RES_CNT  ] = '{0},
        parameter bit [RES_CNT-1:0]     RES_MASK            = '0,   // result is a mask
        parameter bit [RES_CNT-1:0]     RES_NARROW          = '0,   // result may be narrow
        parameter bit [RES_CNT-1:0]     RES_ALLOW_ELEMWISE  = '0,   // result may be 1 elem
        parameter bit [RES_CNT-1:0]     RES_ALWAYS_ELEMWISE = '0,   // result is 1 elem
        parameter bit [RES_CNT-1:0]     RES_ALWAYS_VREG     = '0,   // result is 1 elem
        parameter bit                   FIELD_COUNT_USED    = 1'b0,
        parameter int unsigned          FIELD_OP            = 0,    // op incremented for each field
        parameter int unsigned           VLSU_QUEUE_SZ     = 4,
        parameter bit [VLSU_FLAGS_W-1:0] VLSU_FLAGS        = '0,
        parameter mul_type               MUL_TYPE          = MUL_GENERIC,
        parameter type                  INIT_STATE_T        = logic,
        parameter bit                   DONT_CARE_ZERO      = 1'b0  // initialize don't care values to zero
    )(
        input  logic                    clk_i,
        input  logic                    async_rst_ni,
        input  logic                    sync_rst_ni,

        input  logic                    pipe_in_valid_i,
        output logic                    pipe_in_ready_o,
        input  INIT_STATE_T             pipe_in_state_i,

        input  logic [31:0]             vreg_pend_wr_i,
        output logic [31:0]             vreg_pend_rd_o,
        input  logic [31:0]             vreg_pend_rd_i,

        input  instr_state [XIF_ID_CNT-1:0] instr_state_i,
        output logic                    instr_done_valid_o,
        output logic [XIF_ID_W-1:0]     instr_done_id_o,

        // connections to register file
        output logic [VPORT_CNT-1:0][MAX_VADDR_W-1:0] vreg_rd_addr_o,       // vreg read address
        input  logic [VPORT_CNT-1:0][MAX_VPORT_W-1:0] vreg_rd_data_i,       // vreg read data
        input  logic                [VREG_W     -1:0] vreg_rd_v0_i,         // vreg v0 read data

        output logic                    vreg_wr_valid_o,
        input  logic                    vreg_wr_ready_i,
        output logic [4:0]              vreg_wr_addr_o,
        output logic [VREG_W/8-1:0]     vreg_wr_be_o,
        output logic [VREG_W  -1:0]     vreg_wr_data_o,
        output logic                    vreg_wr_clr_o,
        output logic [1:0]              vreg_wr_clr_cnt_o,

        output logic                    pending_load_o,
        output logic                    pending_store_o,

        vproc_xif.coproc_mem            xif_mem_if,
        vproc_xif.coproc_mem_result     xif_memres_if,

        output logic                    trans_complete_valid_o,
        input  logic                    trans_complete_ready_i,
        output logic [XIF_ID_W-1:0]     trans_complete_id_o,
        output logic                    trans_complete_exc_o,
        output logic [5:0]              trans_complete_exccode_o,

        output logic                    xreg_valid_o,
        input  logic                    xreg_ready_i,
        output logic [XIF_ID_W-1:0]     xreg_id_o,
        output logic [4:0]              xreg_addr_o,
        output logic [31:0]             xreg_data_o
    );

    if ((MAX_OP_W & (MAX_OP_W - 1)) != 0 || MAX_OP_W < 32 || MAX_OP_W >= VREG_W) begin
        $fatal(1, "The vector pipeline operand width MAX_OP_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", MAX_OP_W);
    end

    // Counter operand width (i.e., the operand width that serves to determine the counter width).
    // If element-wise operation may be required the counter operand width is always 8 bit (i.e.,
    // the smallest element width), otherwise the counter operand width is the default width.
    localparam int unsigned COUNTER_OP_W = (
        (OP_ALLOW_ELEMWISE != '0) | (OP_ALWAYS_ELEMWISE != '0)
    ) ? 8 : MAX_OP_W;

    localparam int unsigned COUNTER_W     = $clog2(VREG_W / COUNTER_OP_W) + 4;
    localparam int unsigned AUX_COUNTER_W = $clog2(VREG_W / MAX_OP_W    );

    typedef union packed {
        logic [COUNTER_W-1:0] val;
        struct packed {
            logic                 sign; // sign bit (only used for down slide operations)
            logic [2:0]           mul;  // mul part (vreg index)
            logic [COUNTER_W-5:0] low;  // counter part in vreg (vreg pos)
        } part;
    } counter_t;

    typedef struct packed {
        counter_t                        count;          // main counter
        counter_t                        alt_count;      // alternative counter (used by some ops)
        count_inc_e                      count_inc;      // counter increment policy
        logic        [AUX_COUNTER_W-1:0] aux_count;      // auxiliary counter (for dyn addr ops)
        logic                      [2:0] field_count;    // field counter (for segment loads/stores)
        logic                            first_cycle;
        logic                            last_cycle;
        logic                            alt_last_cycle;
        logic                            init_addr;      // initialize address (used by LSU)
        logic                            requires_flush;
        logic                            red_op;
        logic        [XIF_ID_W     -1:0] id;
        op_unit                          unit;
        op_mode                          mode;
        cfg_vsew                         eew;            // effective element width
        cfg_emul                         emul;           // effective MUL factor
        cfg_vxrm                         vxrm;
        logic        [CFG_VL_W     -1:0] vl;
        logic                            vl_0;
        logic                     [31:0] xval;
        unpack_flags [OP_CNT -1:0]       op_flags;
        logic        [OP_CNT -1:0]       op_load;
        logic        [OP_CNT -1:0][4 :0] op_vaddr;
        logic        [OP_CNT -1:0][31:0] op_xval;
        logic        [RES_CNT-1:0]       res_vreg;
        logic        [RES_CNT-1:0]       res_narrow;
        logic                     [4 :0] res_vaddr;
        logic                     [31:0] pend_vreg_wr;   // pending vector register writes
    } state_t;


    ///////////////////////////////////////////////////////////////////////////
    // STATE LOGIC

    logic        state_valid_q,          state_valid_d;
    logic        state_wait_alt_count_q, state_wait_alt_count_d; // wait for last cycle of alt_count
    state_t      state_q,                state_d;
    logic        state_ready;
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_pipeline_state_valid
        if (~async_rst_ni) begin
            state_valid_q          <= 1'b0;
            state_wait_alt_count_q <= 1'b0;
        end
        else if (~sync_rst_ni) begin
            state_valid_q          <= 1'b0;
            state_wait_alt_count_q <= 1'b0;
        end else begin
            state_valid_q          <= state_valid_d;
            state_wait_alt_count_q <= state_wait_alt_count_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_pipeline_state
        state_q <= state_d;
    end

    // State update logic
    state_t            state_next;
    counter_t          count_next_inc,  alt_count_next_inc;
    logic              last_cycle_next, alt_last_cycle_next, wait_alt_count_next;
    logic [OP_CNT-1:0] op_load_next, op_shift_next;
    logic              vcompress_flushing;
    always_comb begin
        state_valid_d          = state_valid_q;
        state_wait_alt_count_d = state_wait_alt_count_q;
        state_d                = state_q;
        if (state_ready) begin
            state_wait_alt_count_d = wait_alt_count_next;
            state_d                = state_next;
            state_d.last_cycle     = last_cycle_next;
            state_d.alt_last_cycle = alt_last_cycle_next;
            state_d.op_load        = op_load_next;
            for (int i = 0; i < OP_CNT; i++) begin
                state_d.op_flags[i].shift = op_shift_next[i];
            end
        end
        state_d.pend_vreg_wr = state_q.pend_vreg_wr & vreg_pend_wr_i;
        if (pipe_in_ready_o) begin
            state_valid_d        = pipe_in_valid_i;
            state_d.pend_vreg_wr = vreg_pend_wr_i;
        end
    end
    assign wait_alt_count_next = (state_wait_alt_count_q | state_q.last_cycle) & (OP_ALT_COUNTER != 0) & ~state_q.alt_last_cycle;

    logic state_stall, unpack_ready;
    logic state_done;                // the current instruction is done, next can be accepted
    assign state_ready     = ~state_valid_q | (~state_stall & unpack_ready);
    assign state_done      = ((OP_ALT_COUNTER == 0) ? state_q.last_cycle : (
        (state_q.last_cycle | state_wait_alt_count_q) & ~wait_alt_count_next
    )) & (~FIELD_COUNT_USED | (state_q.field_count == '0));
    assign pipe_in_ready_o = state_ready & (~state_valid_q | state_done);

    // Identify whether the auxiliary counter is used
    logic aux_count_used;
    always_comb begin
        aux_count_used = '0;
        for (int i = 0; i < OP_CNT; i++) begin
            if (OP_DYN_ADDR[i] & (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg)) begin
                aux_count_used = 1'b1;
            end
        end
    end

    // Next-state logic
    always_comb begin
        state_next = state_q;
        if (pipe_in_ready_o) begin
            state_next.count = '0;
            if (pipe_in_state_i.count_extra_phase) begin
                state_next.count.part.sign = '1;
                state_next.count.part.mul  = '1;
            end
            state_next.alt_count.val           = {pipe_in_state_i.alt_count_init, {$clog2(MAX_OP_W/COUNTER_OP_W){1'b0}}};
            state_next.count_inc               = pipe_in_state_i.count_inc;
            state_next.aux_count = '1;
            for (int i = 0; i < OP_CNT; i++) begin
                if (OP_DYN_ADDR[i] & (OP_ALWAYS_VREG[i] | pipe_in_state_i.op_flags[i].vreg)) begin
                    state_next.aux_count = '0;
                end
            end
            state_next.field_count             = pipe_in_state_i.field_count_init;
            state_next.first_cycle             = 1'b1;
            state_next.init_addr               = 1'b1;
            state_next.requires_flush          = pipe_in_state_i.requires_flush;
            state_next.red_op                  = pipe_in_state_i.red_op;
            state_next.id                      = pipe_in_state_i.id;
            state_next.unit                    = pipe_in_state_i.unit;
            state_next.mode                    = pipe_in_state_i.mode;
            state_next.eew                     = pipe_in_state_i.eew;
            state_next.emul                    = pipe_in_state_i.emul;
            state_next.vxrm                    = pipe_in_state_i.vxrm;
            state_next.vl                      = pipe_in_state_i.vl;
            state_next.vl_0                    = pipe_in_state_i.vl_0;
            state_next.xval                    = pipe_in_state_i.xval;
            state_next.op_flags                = pipe_in_state_i.op_flags;
            state_next.op_vaddr                = pipe_in_state_i.op_vaddr;
            state_next.op_xval                 = pipe_in_state_i.op_xval;
            state_next.res_vreg                = pipe_in_state_i.res_vreg;
            state_next.res_narrow              = pipe_in_state_i.res_narrow;
            state_next.res_vaddr               = pipe_in_state_i.res_vaddr;
        end else begin
            state_next.first_cycle = '0;
            state_next.init_addr = '0;
            state_next.count     = count_next_inc;
            state_next.alt_count = alt_count_next_inc;
            if (aux_count_used) begin
                state_next.aux_count = state_q.aux_count + AUX_COUNTER_W'(1);
            end
            if (FIELD_COUNT_USED & state_q.last_cycle & state_q.alt_last_cycle) begin
                state_next.init_addr   = 1'b1;
                state_next.count       = '0;
                state_next.alt_count   = '0;
                state_next.field_count = state_q.field_count - 3'b001;
                state_next.xval        = DONT_CARE_ZERO ? '0 : 'x;
                unique case (state_q.eew)
                    VSEW_8:  state_next.xval = state_q.xval + 32'h1;
                    VSEW_16: state_next.xval = state_q.xval + 32'h2;
                    VSEW_32: state_next.xval = state_q.xval + 32'h4;
                    default: ;
                endcase
                state_next.op_vaddr[FIELD_OP] = DONT_CARE_ZERO ? '0 : 'x;
                unique case (state_q.emul)
                    EMUL_1: state_next.op_vaddr[FIELD_OP] = state_q.op_vaddr[FIELD_OP] + 5'(1);
                    EMUL_2: state_next.op_vaddr[FIELD_OP] = state_q.op_vaddr[FIELD_OP] + 5'(2);
                    EMUL_4: state_next.op_vaddr[FIELD_OP] = state_q.op_vaddr[FIELD_OP] + 5'(4);
                    // EMUL_8 is invalid since EMUL * NFIELDS <= 8 according to spec
                    default: ;
                endcase
                state_next.res_vaddr = DONT_CARE_ZERO ? '0 : 'x;
                unique case (state_q.emul)
                    EMUL_1: state_next.res_vaddr = state_q.res_vaddr + 5'(1);
                    EMUL_2: state_next.res_vaddr = state_q.res_vaddr + 5'(2);
                    EMUL_4: state_next.res_vaddr = state_q.res_vaddr + 5'(4);
                    // EMUL_8 is invalid since EMUL * NFIELDS <= 8 according to spec
                    default: ;
                endcase
            end
            for (int i = 0; i < OP_CNT; i++) begin
                if ((OP_DYN_ADDR != '0) & ~OP_DYN_ADDR[i]) begin
                    state_next.op_flags[i].hold = state_q.aux_count != '1;
                end
            end
        end
    end

    // Counter increment logic
    always_comb begin
        count_next_inc     = state_q.count;
        alt_count_next_inc = state_q.alt_count.val;
        if ((OP_DYN_ADDR == '0) | (state_q.aux_count == '1)) begin
            unique case (state_q.count_inc)
                COUNT_INC_1: begin
                    count_next_inc.val     = state_q.count.val     + COUNTER_W'(1);
                    alt_count_next_inc.val = state_q.alt_count.val + COUNTER_W'(1);
                end
                COUNT_INC_2: begin
                    count_next_inc.val     = state_q.count.val     + COUNTER_W'(2);
                    alt_count_next_inc.val = state_q.alt_count.val + COUNTER_W'(2);
                end
                COUNT_INC_4: begin
                    count_next_inc.val     = state_q.count.val     + COUNTER_W'(4);
                    alt_count_next_inc.val = state_q.alt_count.val + COUNTER_W'(4);
                end
                COUNT_INC_MAX: begin
                    count_next_inc.val     = state_q.count.val     + (1 << $clog2(MAX_OP_W/COUNTER_OP_W));
                    alt_count_next_inc.val = state_q.alt_count.val + (1 << $clog2(MAX_OP_W/COUNTER_OP_W));
                end
                default: ;
            endcase
        end
    end

    // Last cycle logic
    always_comb begin
        last_cycle_next     = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        alt_last_cycle_next = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        // first cycle is not last cycle unless EMUL is 1 and the counter has no low part
        if (~state_valid_q | state_done) begin
            // TODO take exceptions into account (OP_ALT_COUNTER != 0 and auxiliary counter)
            last_cycle_next     = (pipe_in_state_i.emul == EMUL_1) & (COUNTER_W == 4);
            alt_last_cycle_next = (pipe_in_state_i.emul == EMUL_1) & (COUNTER_W == 4);
        end else begin
            last_cycle_next     =     count_next_inc.val[COUNTER_W-5:$clog2(MAX_OP_W/COUNTER_OP_W)] == '1;
            alt_last_cycle_next = alt_count_next_inc.val[COUNTER_W-5:$clog2(MAX_OP_W/COUNTER_OP_W)] == '1;
            // clear last cycle in case lower bits are not set for lower counter increments
            unique case (state_q.count_inc)
                COUNT_INC_1: for (int i = 0; i < $clog2(MAX_OP_W/COUNTER_OP_W); i++) begin
                    last_cycle_next     &=     count_next_inc.val[i];
                    alt_last_cycle_next &= alt_count_next_inc.val[i];
                end
                COUNT_INC_2: for (int i = 1; i < $clog2(MAX_OP_W/COUNTER_OP_W); i++) begin
                    last_cycle_next     &=     count_next_inc.val[i];
                    alt_last_cycle_next &= alt_count_next_inc.val[i];
                end
                COUNT_INC_4: for (int i = 2; i < $clog2(MAX_OP_W/COUNTER_OP_W); i++) begin
                    last_cycle_next     &=     count_next_inc.val[i];
                    alt_last_cycle_next &= alt_count_next_inc.val[i];
                end
                default: ;
            endcase
            if (state_q.requires_flush) begin
                last_cycle_next &= vcompress_flushing;
            end else begin
            // clear last cycle based on EMUL (note: the alt_last_cycle signal is not cleared here
            // as that is only required to indicate completion of one vreg cycle)
            unique case (state_q.emul)
                EMUL_2: last_cycle_next &= count_next_inc.part.mul[  0] == '1;
                EMUL_4: last_cycle_next &= count_next_inc.part.mul[1:0] == '1;
                EMUL_8: last_cycle_next &= count_next_inc.part.mul[2:0] == '1;
                default: ;
            endcase
            end
            if ((OP_ALT_COUNTER != '0) & state_q.count.part.sign) begin
                last_cycle_next = '0;
            end
            if (aux_count_used & ((state_q.aux_count ^ AUX_COUNTER_W'(1)) != '1)) begin
                last_cycle_next = '0;
            end
        end
    end

    // Extra cycles for flushing output in vcompress
    always_comb begin
        vcompress_flushing = 1'b0;
        unique case (state_q.emul)
            EMUL_1: vcompress_flushing = count_next_inc.part.mul[0] == 1'b1;
            EMUL_2: vcompress_flushing = count_next_inc.part.mul[1] == 1'b1;
            EMUL_4: vcompress_flushing = count_next_inc.part.mul[2] == 1'b1;
            EMUL_8: vcompress_flushing = count_next_inc.part.sign   == 1'b1;
            default: ;
        endcase
        // Doesn't make sense to consider the vcompress_flushing when starting the pipe operation
        vcompress_flushing &= ~pipe_in_ready_o;
    end

    // Operand load and shift signals
    counter_t [OP_CNT-1:0] op_count;
    always_comb begin
        for (int i = 0; i < OP_CNT; i++) begin
            // use next value of counter rather than current (including potential new instruction)
            op_count[i] = OP_ALT_COUNTER[i] ? state_next.alt_count : state_next.count;
        end
    end
    always_comb begin
        op_load_next  = '0;
        op_shift_next = '0;
        for (int i = 0; i < OP_CNT; i++) begin
            if (OP_DYN_ADDR[i]) begin
                if (state_next.aux_count == '0) begin
                    op_load_next[i] = OP_ALWAYS_VREG[i] | state_next.op_flags[i].vreg;
                end
                op_shift_next[i] = 1'b1;
            end
            // Regular operands are only fetched if the auxiliary counter is either not used or is
            // zero in the next cycle.  Note that aux_count_used may be incorrect if a new
            // instruction is currently being loaded (i.e., pipe_in_ready_o is asserted), in which
            // case the operands should be fetched regardless of the next auxilary counter value
            // (which may be non-zero if the auxiliary counter is not used by the new instruction)
            else if (~aux_count_used | (state_next.aux_count == '0) | pipe_in_ready_o) begin
                if (~OP_MASK[i]) begin
                    if ((op_count[i].part.low == '0) &
                        (~OP_NARROW[i] | ~state_next.op_flags[i].narrow | ~op_count[i].part.mul[0]) &
                        (~state_next.requires_flush | ~vcompress_flushing) // We don't load ops for vcompress when flushing
                    ) begin
                        op_load_next[i] = OP_ALWAYS_VREG[i] | state_next.op_flags[i].vreg;

                        // if the alternative counter is used for some operands the counter's
                        // sign and MUL part might be invalid for the current EMUL, in which
                        // case the load needs to be suppressed
                        if (OP_ALT_COUNTER != '0) begin
                            unique case (state_next.emul)
                                EMUL_1: if (  op_count[i].val[COUNTER_W-1 -: 4]             != '0) begin
                                    op_load_next[i] = '0;
                                end
                                EMUL_2: if (((op_count[i].val[COUNTER_W-1 -: 4]) & 4'b1110) != '0) begin
                                    op_load_next[i] = '0;
                                end
                                EMUL_4: if (((op_count[i].val[COUNTER_W-1 -: 4]) & 4'b1100) != '0) begin
                                    op_load_next[i] = '0;
                                end
                                EMUL_8: if (((op_count[i].val[COUNTER_W-1 -: 4]) & 4'b1000) != '0) begin
                                    op_load_next[i] = '0;
                                end
                                default: ;
                            endcase
                        end
                    end

                    // Operands are shifted after OP_W bits have been consumed.
                    if ((op_count[i].val & ~({COUNTER_W{1'b1}} << $clog2(OP_W[i] / COUNTER_OP_W))) == '0) begin
                        op_shift_next[i] = ~OP_NARROW[i] | ~state_next.op_flags[i].narrow |
                                           ~op_count[i].val[$clog2(OP_W[i] / COUNTER_OP_W)];
                    end
                end else begin
                    // Masks are only fetched in the first cycle but never anytime later
                    if (op_count[i].val == '0) begin
                        op_load_next[i] = OP_ALWAYS_VREG[i] | state_next.op_flags[i].vreg;
                    end
                    // The amount of mask bits consumed each cycle depends on the element width
                    if ((op_count[i].val & ~({COUNTER_W{1'b1}} << $clog2(OP_W[i] / (COUNTER_OP_W / 8)))) == '0) begin
                        op_shift_next[i] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case (state_next.eew)
                            VSEW_8:  op_shift_next[i] = 1'b1;
                            VSEW_16: op_shift_next[i] = op_count[i].val[$clog2(OP_W[i] / (COUNTER_OP_W / 8))     ] == '0;
                            VSEW_32: op_shift_next[i] = op_count[i].val[$clog2(OP_W[i] / (COUNTER_OP_W / 8)) +: 2] == '0;
                            default: ;
                        endcase
                    end
                end
            end
        end
        // do not load anything while waiting for the last cycle of the alt counter
        if (wait_alt_count_next) begin
            op_load_next = '0;
        end
    end

    // Result store and shift signals
    logic res_store;
    logic res_shift;
    always_comb begin
        res_store = '0;
        res_shift = '0;
        // Store uses next counter value (after increment, but not taking into account a potential
        // new instruction) and current state (i.e., also disregarding new instructions)
        // TODO consider the auxiliary counter
        if ((count_next_inc.part.low == '0) & ((OP_ALT_COUNTER == '0) | ~state_q.count.part.sign) &
            ((RES_ALWAYS_VREG | state_q.res_vreg) != '0) // at least one valid vreg
        ) begin
            res_store = ((RES_NARROW & state_q.res_narrow) == '0) | ~count_next_inc.part.mul[0];
        end
        // Shifting is delayed by one cycle compared to the store and hence uses the current counter
        if ((state_q.count.val & ~({COUNTER_W{1'b1}} << $clog2(RES_W[0] / COUNTER_OP_W))) == '0) begin
            res_shift = ((RES_NARROW & state_q.res_narrow) == '0) |
                        ~state_q.count[$clog2(RES_W[0] / COUNTER_OP_W)];
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // OPERAND ADDRESS, FLAGS, AND READ SIGNAL GENERATION

    unpack_flags [OP_CNT-1:0]       op_flags;
    logic        [OP_CNT-1:0]       op_load;
    logic        [OP_CNT-1:0][4 :0] op_vaddr;
    logic        [OP_CNT-1:0][31:0] op_xval;
    always_comb begin
        op_flags = state_q.op_flags;
        op_vaddr = state_q.op_vaddr;
        op_xval  = state_q.op_xval;
        for (int i = 0; i < OP_CNT; i++) begin
            op_load [i]       = state_q.op_load [i];
            op_flags[i].shift = state_q.op_flags[i].shift;
            if (state_q.op_load[i] & ~OP_DYN_ADDR[i]) begin
                if (OP_NARROW[i] & state_q.op_flags[i].narrow) begin
                    op_vaddr[i][1:0] = state_q.op_vaddr[i][1:0] | (OP_ALT_COUNTER[i] ? state_q.alt_count.part.mul[2:1] : state_q.count.part.mul[2:1]);
                end else begin
                    op_vaddr[i][2:0] = state_q.op_vaddr[i][2:0] | (OP_ALT_COUNTER[i] ? state_q.alt_count.part.mul      : state_q.count.part.mul     );
                end
            end
            if (OP_ALT_COUNTER[i]) begin
                op_flags[i].vreg = OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg;
                unique case (state_q.emul)
                    EMUL_1: if (  state_q.alt_count.val[COUNTER_W-1 -: 4]             != '0) begin
                        op_flags[i].vreg = '0;
                    end
                    EMUL_2: if (((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1110) != '0) begin
                        op_flags[i].vreg = '0;
                    end
                    EMUL_4: if (((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1100) != '0) begin
                        op_flags[i].vreg = '0;
                    end
                    EMUL_8: if (((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1000) != '0) begin
                        op_flags[i].vreg = '0;
                    end
                    default: ;
                endcase
            end
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // PENDING VECTOR REGISTER READS

    // Potential pending reads of an operand with dynamic address offset
    logic [31:0] op_addr_offset_pend_reads;
    logic [31:0] op_addr_offset_pend_reads_q, op_addr_offset_pend_reads_d;
    logic        op_addr_offset_pend_reads_clear;
    always_ff @(posedge clk_i or negedge async_rst_ni) begin
        if (~async_rst_ni) begin
            op_addr_offset_pend_reads_q <= '0;
        end
        else if (~sync_rst_ni) begin
            op_addr_offset_pend_reads_q <= '0;
        end
        else begin
            op_addr_offset_pend_reads_q <= op_addr_offset_pend_reads_d;
        end
    end
    always_comb begin
        op_addr_offset_pend_reads = '0;
        if (OP_DYN_ADDR != '0) begin
            op_addr_offset_pend_reads = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_q.emul)
                EMUL_1: op_addr_offset_pend_reads = 32'h01 <<  state_q.op_vaddr[$clog2(OP_DYN_ADDR)];
                EMUL_2: op_addr_offset_pend_reads = 32'h03 << {state_q.op_vaddr[$clog2(OP_DYN_ADDR)][4:1], 1'b0};
                EMUL_4: op_addr_offset_pend_reads = 32'h0F << {state_q.op_vaddr[$clog2(OP_DYN_ADDR)][4:2], 2'b0};
                EMUL_8: op_addr_offset_pend_reads = 32'hFF << {state_q.op_vaddr[$clog2(OP_DYN_ADDR)][4:3], 3'b0};
                default: ;
            endcase
        end
    end
    always_comb begin
        op_addr_offset_pend_reads_d = op_addr_offset_pend_reads_q;
        if (op_addr_offset_pend_reads_clear) begin
            op_addr_offset_pend_reads_d = '0;
        end
        if (state_valid_q & ~state_stall) begin
            op_addr_offset_pend_reads_d |= op_addr_offset_pend_reads;
        end
    end

    logic [OP_CNT-1:0][31:0] op_pend_reads;
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            always_comb begin
                op_pend_reads[i] = '0;
                if (OP_DYN_ADDR[i]) begin
                    if (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg) begin
                        op_pend_reads[i] = op_addr_offset_pend_reads_q;
                    end
                end
                else if (OP_MASK[i]) begin
                    if ((OP_ALT_COUNTER != '0) & (OP_ALT_COUNTER[i] ? state_q.alt_count.part.sign : state_q.count.part.sign) & (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg)) begin
                        op_pend_reads[i] = (OP_SRC[i] >= VPORT_CNT) ? '0 : (32'b1 << state_q.op_vaddr[i]);
                    end
                end
                // TODO guard with VPORT_ADDR_ZERO[OP_SRC[i]]
                else if (OP_ALT_COUNTER[i]) begin
                    //if (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg) begin
                        op_pend_reads[i] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case ({state_q.emul, OP_NARROW[i] & state_q.op_flags[i].narrow})
                            {EMUL_1, 1'b1},
                            {EMUL_1, 1'b0},
                            {EMUL_2, 1'b1}: op_pend_reads[i] = 32'h01 <<  state_q.op_vaddr[i];
                            {EMUL_2, 1'b0},
                            {EMUL_4, 1'b1}: op_pend_reads[i] = 32'h03 << {state_q.op_vaddr[i][4:1], 1'b0};
                            {EMUL_4, 1'b0},
                            {EMUL_8, 1'b1}: op_pend_reads[i] = 32'h0F << {state_q.op_vaddr[i][4:2], 2'b0};
                            {EMUL_8, 1'b0}: op_pend_reads[i] = 32'hFF << {state_q.op_vaddr[i][4:3], 3'b0};
                            default: ;
                        endcase
                    //end
                end
                //else if (OP_ALT_COUNTER != '0) begin
                //end
                // In the second part of vcompress, we don't generate extra pending reads
                else if(~state_q.requires_flush | (~vcompress_flushing & ~state_done)) begin
                    if (OP_ALWAYS_VREG[i] | state_q.op_flags[i].vreg) begin
                        op_pend_reads[i] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case ({state_q.emul, OP_NARROW[i] & state_q.op_flags[i].narrow})
                            {EMUL_1, 1'b1},
                            {EMUL_1, 1'b0},
                            {EMUL_2, 1'b1}: op_pend_reads[i] = '0;
                            {EMUL_2, 1'b0}: op_pend_reads[i] = (32'h03 & (32'h02 << state_q.count.part.mul[2:0])) << {state_q.op_vaddr[i][4:1], 1'b0};
                            {EMUL_4, 1'b1}: op_pend_reads[i] = (32'h03 & (32'h02 << state_q.count.part.mul[2:1])) << {state_q.op_vaddr[i][4:1], 1'b0};
                            {EMUL_4, 1'b0}: op_pend_reads[i] = (32'h0F & (32'h0E << state_q.count.part.mul[2:0])) << {state_q.op_vaddr[i][4:2], 2'b0};
                            {EMUL_8, 1'b1}: op_pend_reads[i] = (32'h0F & (32'h0E << state_q.count.part.mul[2:1])) << {state_q.op_vaddr[i][4:2], 2'b0};
                            {EMUL_8, 1'b0}: op_pend_reads[i] = (32'hFF & (32'hFE << state_q.count.part.mul[2:0])) << {state_q.op_vaddr[i][4:3], 3'b0};
                            default: ;
                        endcase
                    end
                end
            end
        end
    endgenerate

    // add further vregs that are read if multiple fields are used (note that the operand
    // address is incremented as the field count is decremented)
    // TODO make this generic for some specified operand instead of always using operand 1
    logic [31:0] op_fields_pend_reads;
    always_comb begin
        op_fields_pend_reads = '0;
        if (OP_ALWAYS_VREG[FIELD_OP] | state_q.op_flags[FIELD_OP].vreg) begin
            for (int i = 0; 3'(i) < state_q.field_count; i++) begin
                unique case (state_q.emul)
                    EMUL_1: op_fields_pend_reads |= (32'h1 <<  (i + 1)     ) <<  state_q.op_vaddr[FIELD_OP]            ;
                    EMUL_2: op_fields_pend_reads |= (32'h3 << ((i + 1) * 2)) << {state_q.op_vaddr[FIELD_OP][4:1], 1'b0};
                    EMUL_4: op_fields_pend_reads |= (32'hF << ((i + 1) * 4)) << {state_q.op_vaddr[FIELD_OP][4:2], 2'b0};
                    // EMUL_8 cannot be used with multiple fields
                    default: ;
                endcase
            end
        end
    end

    logic [31:0] op_pend_reads_all;
    always_comb begin
        op_pend_reads_all = FIELD_COUNT_USED ? op_fields_pend_reads : '0;
        for (int i = 0; i < OP_CNT; i++) begin
            op_pend_reads_all |= op_pend_reads[i];
            if (op_load[i]) begin
                if (OP_DYN_ADDR[i]) begin
                    op_pend_reads_all |= op_addr_offset_pend_reads;
                end else begin
                    op_pend_reads_all[(OP_SRC[i] >= VPORT_CNT) ? '0 : op_vaddr[i]] = 1'b1;
                end
            end
        end
    end

    logic [31:0] unpack_pend_rd;
    assign vreg_pend_rd_o = state_valid_q ? ((op_pend_reads_all & ~state_q.pend_vreg_wr) | unpack_pend_rd) : '0;


    ///////////////////////////////////////////////////////////////////////////
    // STALLING LOGIC

    // Stall vreg reads until pending writes are complete; note that vreg read stalling always
    // happens in the first stage, since otherwise a substantial amount of state would have to be
    // forwarded (such as vreg_pend_wr_q)
    always_comb begin
        state_stall = '0;
        for (int i = 0; i < OP_CNT; i++) begin
            if (OP_DYN_ADDR[i]) begin
                state_stall |= op_load[i] & ((op_addr_offset_pend_reads & state_q.pend_vreg_wr) != '0);
            end else begin
                state_stall |= op_load[i] & state_q.pend_vreg_wr[(OP_SRC[i] >= VPORT_CNT) ? '0 : op_vaddr[i]];
            end
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // UNIT CONTROL SIGNALS

    typedef struct packed {
        logic [2:0]                    count_mul;
        logic                          first_cycle;
        logic                          last_cycle;
        logic                          init_addr;       // initialize address (used by LSU)
        logic                          requires_flush;
        logic                          red_op;
        logic                          alt_count_valid; // alternative counter value is valid
        logic [AUX_COUNTER_W-1:0]      aux_count;
        logic [XIF_ID_W-1:0]           id;
        op_unit                        unit;
        op_mode                        mode;
        cfg_vsew                       eew;             // effective element width
        cfg_emul                       emul;            // effective MUL factor
        cfg_vxrm                       vxrm;
        logic [$clog2(MAX_OP_W/8)-1:0] vl_part;
        logic                          vl_part_0;
        logic                          last_vl_part;    // last VL part that is not 0
        logic                          vl_0;
        logic [31:0]                   xval;
        //logic [RES_CNT-1:0]            res_vreg;
        logic [RES_CNT-1:0]            res_narrow;
        logic                          res_store;
        logic                          res_shift;
        logic [4:0]                    res_vaddr;
        logic                          pend_load;
        logic                          pend_store;
    } ctrl_t;

    logic  unpack_valid;
    ctrl_t unpack_ctrl;
    always_comb begin
        unpack_valid                = state_valid_q & ~state_stall & ~state_wait_alt_count_q;
        unpack_ctrl.count_mul       = state_q.count.part.mul;
        unpack_ctrl.first_cycle     = state_q.first_cycle;
        unpack_ctrl.last_cycle      = state_valid_q & state_q.last_cycle & // TODO remove state_valid_q
                                      (~FIELD_COUNT_USED | (state_q.field_count == '0));
        unpack_ctrl.init_addr       = state_q.init_addr;
        unpack_ctrl.requires_flush  = state_q.requires_flush;
        unpack_ctrl.red_op          = state_q.red_op;
        unpack_ctrl.alt_count_valid = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_q.emul)
            EMUL_1: unpack_ctrl.alt_count_valid =   state_q.alt_count.val[COUNTER_W-1 -: 4]             == '0;
            EMUL_2: unpack_ctrl.alt_count_valid = ((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1110) == '0;
            EMUL_4: unpack_ctrl.alt_count_valid = ((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1100) == '0;
            EMUL_8: unpack_ctrl.alt_count_valid = ((state_q.alt_count.val[COUNTER_W-1 -: 4]) & 4'b1000) == '0;
            default: ;
        endcase
        unpack_ctrl.aux_count = state_q.aux_count;
        unpack_ctrl.id        = state_q.id;
        unpack_ctrl.unit      = state_q.unit;
        unpack_ctrl.mode      = state_q.mode;
        unpack_ctrl.eew       = state_q.eew;
        unpack_ctrl.emul      = state_q.emul;
        unpack_ctrl.vxrm      = state_q.vxrm;

        // Determine the length of the current part of the vector based on the overall VL setting;
        // considers only the relevant counter bits for vl_part; for element-wise operation only
        // vl_part_0 (i.e., whether the length of the current part is 0) is relevant
        unpack_ctrl.vl_part      = (state_q.count.val[COUNTER_W-2:$clog2(MAX_OP_W/COUNTER_OP_W)] == state_q.vl[CFG_VL_W-1:$clog2(MAX_OP_W/8)]) ?  state_q.vl[$clog2(MAX_OP_W/8)-1:0] : '1;
        unpack_ctrl.vl_part_0    = (state_q.count.val[COUNTER_W-2:$clog2(MAX_OP_W/COUNTER_OP_W)] >  state_q.vl[CFG_VL_W-1:$clog2(MAX_OP_W/8)]) |  state_q.vl_0;
        unpack_ctrl.last_vl_part = (state_q.count.val[COUNTER_W-2:$clog2(MAX_OP_W/COUNTER_OP_W)] == state_q.vl[CFG_VL_W-1:$clog2(MAX_OP_W/8)]) & ~state_q.vl_0;
        if ((UNITS[UNIT_LSU ] & (state_q.unit == UNIT_LSU ) & (state_q.mode.lsu.stride != LSU_UNITSTRIDE)) |
            (UNITS[UNIT_ELEM] & (state_q.unit == UNIT_ELEM))
        ) begin
            unpack_ctrl.vl_part_0 = (state_q.count.val[COUNTER_W-2:0] >  state_q.vl[CFG_VL_W-1:$clog2(COUNTER_OP_W/8)]) |  state_q.vl_0;
        end
        unpack_ctrl.vl_0 = state_q.vl_0;

        unpack_ctrl.xval = state_q.xval;
        if (UNITS[UNIT_LSU] & (state_q.unit == UNIT_LSU) & ~state_q.init_addr) begin
            unpack_ctrl.xval = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_q.mode.lsu.stride)
                LSU_STRIDED: unpack_ctrl.xval = state_q.op_xval[0];
                LSU_INDEXED: unpack_ctrl.xval = state_q.xval;
                default: ;
            endcase
        end

        //unpack_ctrl.res_vreg   = state_q.res_vreg;
        unpack_ctrl.res_narrow = state_q.res_narrow;
        unpack_ctrl.res_store  = res_store;
        unpack_ctrl.res_shift  = res_shift;
        unpack_ctrl.res_vaddr  = state_q.res_vaddr;
        for (int i = 0; i < RES_CNT; i++) begin
            if ((state_q.unit != UNIT_ELEM) & ~RES_MASK[i] & (RES_ALWAYS_VREG[i] | state_q.res_vreg[i])) begin
                if (RES_NARROW[i] & state_q.res_narrow[i]) begin
                    unpack_ctrl.res_vaddr[1:0] = state_q.res_vaddr[1:0] | state_q.count.part.mul[2:1];
                end else begin
                    unpack_ctrl.res_vaddr[2:0] = state_q.res_vaddr[2:0] | state_q.count.part.mul;
                end
            end
        end

        // pending loads and stores flags for LSU
        unpack_ctrl.pend_load  = UNITS[UNIT_LSU] & (state_q.unit == UNIT_LSU) & ~state_q.mode.lsu.store;
        unpack_ctrl.pend_store = UNITS[UNIT_LSU] & (state_q.unit == UNIT_LSU) &  state_q.mode.lsu.store;
    end


    ///////////////////////////////////////////////////////////////////////////
    // LSU PENDING LOADS AND STORES SIGNALS

    ctrl_t unpack_ctrl_flags;
    logic  lsu_pending_load, lsu_pending_store;
    assign pending_load_o  = UNITS[UNIT_LSU] & (
                                 (state_valid_q & (state_q.unit == UNIT_LSU) & ~state_q.mode.lsu.store) |
                                 unpack_ctrl_flags.pend_load  | lsu_pending_load
                             );
    assign pending_store_o = UNITS[UNIT_LSU] & (
                                 (state_valid_q & (state_q.unit == UNIT_LSU) &  state_q.mode.lsu.store) |
                                 unpack_ctrl_flags.pend_store | lsu_pending_store
                             );


    ///////////////////////////////////////////////////////////////////////////
    // REGISTER READ/WRITE AND UNIT INSTANTIATION

    // source operand of dynamic address requires hold
    // TODO: does the mask operand (index -1) also require holding?
    localparam bit [OP_CNT-1:0] OP_HOLD_FLAG = (OP_DYN_ADDR != '0) ? (OP_CNT'(1) << OP_DYN_ADDR_SRC) : '0;

    logic [VPORT_CNT-1:0][4:0]          unpack_vreg_addr;
    logic [VPORT_CNT-1:0][VREG_W  -1:0] unpack_vreg_data;
    logic                               unpack_out_valid;
    logic                               unpack_out_ready;
    ctrl_t                              unpack_out_ctrl;
    logic [OP_CNT   -1:0][MAX_OP_W-1:0] unpack_out_ops;
    vproc_vregunpack #(
        .MAX_VPORT_W          ( MAX_VPORT_W                  ),
        .MAX_VADDR_W          ( MAX_VADDR_W                  ),
        .VPORT_CNT            ( VPORT_CNT                    ),
        .VPORT_W              ( VPORT_W                      ),
        .VADDR_W              ( VADDR_W                      ),
        .VPORT_BUFFER         ( VPORT_BUFFER                 ),
        .VPORT_V0_W           ( VREG_W                       ),
        .MAX_OP_W             ( MAX_OP_W                     ),
        .OP_CNT               ( OP_CNT                       ),
        .OP_W                 ( OP_W                         ),
        .OP_STAGE             ( OP_STAGE                     ),
        .OP_SRC               ( OP_SRC                       ),
        .OP_DYN_ADDR_SRC      ( OP_DYN_ADDR_SRC              ),
        .OP_DYN_ADDR          ( OP_DYN_ADDR                  ),
        .OP_MASK              ( OP_MASK                      ),
        .OP_XREG              ( OP_XREG                      ),
        .OP_NARROW            ( OP_NARROW                    ),
        .OP_ALLOW_ELEMWISE    ( OP_ALLOW_ELEMWISE            ),
        .OP_ALWAYS_ELEMWISE   ( OP_ALWAYS_ELEMWISE           ),
        .OP_HOLD_FLAG         ( OP_HOLD_FLAG                 ),
        .UNPACK_STAGES        ( UNPACK_STAGES                ),
        .FLAGS_T              ( unpack_flags                 ),
        .CTRL_DATA_W          ( $bits(ctrl_t)                ),
        .DONT_CARE_ZERO       ( DONT_CARE_ZERO               )
    ) unpack (
        .clk_i                ( clk_i                        ),
        .async_rst_ni         ( async_rst_ni                 ),
        .sync_rst_ni          ( sync_rst_ni                  ),
        .vreg_rd_addr_o       ( vreg_rd_addr_o               ),
        .vreg_rd_data_i       ( vreg_rd_data_i               ),
        .vreg_rd_v0_i         ( vreg_rd_v0_i                 ),
        .pipe_in_valid_i      ( unpack_valid                 ),
        .pipe_in_ready_o      ( unpack_ready                 ),
        .pipe_in_ctrl_i       ( unpack_ctrl                  ),
        .pipe_in_eew_i        ( unpack_ctrl.eew              ),
        .pipe_in_op_load_i    ( op_load                      ),
        .pipe_in_op_vaddr_i   ( op_vaddr                     ),
        .pipe_in_op_flags_i   ( op_flags                     ),
        .pipe_in_op_xval_i    ( op_xval                      ),
        .pipe_out_valid_o     ( unpack_out_valid             ),
        .pipe_out_ready_i     ( unpack_out_ready             ),
        .pipe_out_ctrl_o      ( unpack_out_ctrl              ),
        .pipe_out_op_data_o   ( unpack_out_ops               ),
        .pending_vreg_reads_o ( unpack_pend_rd               ),
        .stage_valid_any_o    (                              ),
        .ctrl_flags_any_o     ( unpack_ctrl_flags            ),
        .ctrl_flags_all_o     (                              )
    );

    assign op_addr_offset_pend_reads_clear = unpack_out_valid & unpack_out_ctrl.last_cycle;

    logic                  lsu_instr_done_valid;
    logic [XIF_ID_W  -1:0] lsu_instr_done_id;

    logic                                   unit_out_valid;
    logic                                   unit_out_ready;
    logic      [XIF_ID_W              -1:0] unit_out_instr_id;
    vproc_pkg::cfg_vsew                     unit_out_eew;
    logic      [4:0]                        unit_out_vaddr;
    logic                                   unit_out_res_vaddr;
    logic      [RES_CNT-1:0]                unit_out_res_store;
    logic      [RES_CNT-1:0]                unit_out_res_valid;
    pack_flags [RES_CNT-1:0]                unit_out_res_flags;
    logic      [RES_CNT-1:0][MAX_RES_W-1:0] unit_out_res_data;
    logic      [RES_CNT-1:0][MAX_RES_W-1:0] unit_out_res_mask;
    logic                                   unit_out_pend_clear;
    logic      [1:0]                        unit_out_pend_clear_cnt;
    logic                                   unit_out_instr_done;
    vproc_unit_mux #(
        .UNITS                     ( UNITS                    ),
        .XIF_ID_W                  ( XIF_ID_W                 ),
        .XIF_ID_CNT                ( XIF_ID_CNT               ),
        .VREG_W                    ( VREG_W                   ),
        .OP_CNT                    ( OP_CNT                   ),
        .MAX_OP_W                  ( MAX_OP_W                 ),
        .RES_CNT                   ( RES_CNT                  ),
        .MAX_RES_W                 ( MAX_RES_W                ),
        .VLSU_QUEUE_SZ             ( VLSU_QUEUE_SZ            ),
        .VLSU_FLAGS                ( VLSU_FLAGS               ),
        .MUL_TYPE                  ( MUL_TYPE                 ),
        .CTRL_T                    ( ctrl_t                   ),
        .COUNTER_T                 ( counter_t                ),
        .COUNTER_W                 ( COUNTER_W                ),
        .DONT_CARE_ZERO            ( DONT_CARE_ZERO           )
    ) unit_mux (
        .clk_i                     ( clk_i                    ),
        .async_rst_ni              ( async_rst_ni             ),
        .sync_rst_ni               ( sync_rst_ni              ),
        .pipe_in_valid_i           ( unpack_out_valid         ),
        .pipe_in_ready_o           ( unpack_out_ready         ),
        .pipe_in_ctrl_i            ( unpack_out_ctrl          ),
        .pipe_in_op_data_i         ( unpack_out_ops           ),
        .pipe_out_valid_o          ( unit_out_valid           ),
        .pipe_out_ready_i          ( unit_out_ready           ),
        .pipe_out_instr_id_o       ( unit_out_instr_id        ),
        .pipe_out_eew_o            ( unit_out_eew             ),
        .pipe_out_vaddr_o          ( unit_out_vaddr           ),
        .pipe_out_res_store_o      ( unit_out_res_store       ),
        .pipe_out_res_valid_o      ( unit_out_res_valid       ),
        .pipe_out_res_flags_o      ( unit_out_res_flags       ),
        .pipe_out_res_data_o       ( unit_out_res_data        ),
        .pipe_out_res_mask_o       ( unit_out_res_mask        ),
        .pipe_out_pend_clear_o     ( unit_out_pend_clear      ),
        .pipe_out_pend_clear_cnt_o ( unit_out_pend_clear_cnt  ),
        .pipe_out_instr_done_o     ( unit_out_instr_done      ),
        .pending_load_o            ( lsu_pending_load         ),
        .pending_store_o           ( lsu_pending_store        ),
        .vreg_pend_rd_i            ( vreg_pend_rd_i           ),
        .instr_state_i             ( instr_state_i            ),
        .xif_mem_if                ( xif_mem_if               ),
        .xif_memres_if             ( xif_memres_if            ),
        .trans_complete_valid_o    ( trans_complete_valid_o   ),
        .trans_complete_ready_i    ( trans_complete_ready_i   ),
        .trans_complete_id_o       ( trans_complete_id_o      ),
        .trans_complete_exc_o      ( trans_complete_exc_o     ),
        .trans_complete_exccode_o  ( trans_complete_exccode_o ),
        .xreg_valid_o              ( xreg_valid_o             ),
        .xreg_ready_i              ( xreg_ready_i             ),
        .xreg_id_o                 ( xreg_id_o                ),
        .xreg_addr_o               ( xreg_addr_o              ),
        .xreg_data_o               ( xreg_data_o              )
    );


    // TODO assert that vreg_pend_rd_i, instr_spec_i, and instr_killed_i do not affect LSU
    // instructions (which cannot be stalled beyond the request stage)
    vproc_vregpack #(
        .VPORT_W                     ( VREG_W                  ),
        .VADDR_W                     ( 5                       ),
        .MAX_RES_W                   ( MAX_RES_W               ),
        .RES_CNT                     ( RES_CNT                 ),
        .RES_W                       ( RES_W                   ),
        .RES_MASK                    ( RES_MASK                ),
        .RES_NARROW                  ( RES_NARROW              ),
        .RES_ALLOW_ELEMWISE          ( RES_ALLOW_ELEMWISE      ),
        .RES_ALWAYS_ELEMWISE         ( RES_ALWAYS_ELEMWISE     ),
        .FLAGS_T                     ( pack_flags              ),
        .INSTR_ID_W                  ( XIF_ID_W                ),
        .INSTR_ID_CNT                ( XIF_ID_CNT              ),
        .DONT_CARE_ZERO              ( DONT_CARE_ZERO          )
    ) pack (
        .clk_i                       ( clk_i                   ),
        .async_rst_ni                ( async_rst_ni            ),
        .sync_rst_ni                 ( sync_rst_ni             ),
        .pipe_in_valid_i             ( unit_out_valid          ),
        .pipe_in_ready_o             ( unit_out_ready          ),
        .pipe_in_instr_id_i          ( unit_out_instr_id       ),
        .pipe_in_eew_i               ( unit_out_eew            ),
        .pipe_in_vaddr_i             ( unit_out_vaddr          ),
        .pipe_in_res_store_i         ( unit_out_res_store      ),
        .pipe_in_res_valid_i         ( unit_out_res_valid      ),
        .pipe_in_res_flags_i         ( unit_out_res_flags      ),
        .pipe_in_res_data_i          ( unit_out_res_data       ),
        .pipe_in_res_mask_i          ( unit_out_res_mask       ),
        .pipe_in_pend_clr_i          ( unit_out_pend_clear     ),
        .pipe_in_pend_clr_cnt_i      ( unit_out_pend_clear_cnt ),
        .pipe_in_instr_done_i        ( unit_out_instr_done     ),
        .vreg_wr_valid_o             ( vreg_wr_valid_o         ),
        .vreg_wr_ready_i             ( vreg_wr_ready_i         ),
        .vreg_wr_addr_o              ( vreg_wr_addr_o          ),
        .vreg_wr_be_o                ( vreg_wr_be_o            ),
        .vreg_wr_data_o              ( vreg_wr_data_o          ),
        .vreg_wr_clr_o               ( vreg_wr_clr_o           ),
        .vreg_wr_clr_cnt_o           ( vreg_wr_clr_cnt_o       ),
        .pending_vreg_reads_i        ( vreg_pend_rd_i          ),
        .instr_state_i               ( instr_state_i           ),
        .instr_done_valid_o          ( instr_done_valid_o      ),
        .instr_done_id_o             ( instr_done_id_o         )
    );


`ifdef VPROC_SVA
`include "vproc_pipeline_sva.svh"
`endif

endmodule
