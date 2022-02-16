// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_lsu #(
        parameter int unsigned        VREG_W          = 128,  // width in bits of vector registers
        parameter int unsigned        VMSK_W          = 16,   // width of vector register masks (= VREG_W / 8)
        parameter int unsigned        VMEM_W          = 32,   // width in bits of the vector memory interface
        parameter int unsigned        CFG_VL_W        = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned        XIF_ID_W        = 3,    // width in bits of instruction IDs
        parameter int unsigned        XIF_ID_CNT      = 8,    // total count of instruction IDs
        parameter int unsigned        MAX_WR_ATTEMPTS = 1,    // max required vregfile write attempts
        parameter bit                 BUF_VREG        = 1'b1, // insert pipeline stage after vreg read
        parameter bit                 BUF_REQUEST     = 1'b1, // insert pipeline stage before issuing request
        parameter bit                 BUF_RDATA       = 1'b1, // insert pipeline stage after memory read
        parameter bit                 DONT_CARE_ZERO  = 1'b0  // initialize don't care values to zero
    )
    (
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
        output logic                  misaligned_o,

        input  vproc_pkg::op_mode_lsu mode_i,
        input  vproc_pkg::op_regs     rs1_i,
        input  vproc_pkg::op_regs     rs2_i,
        input  logic [4:0]            vd_i,

        output logic                  pending_load_o,
        output logic                  pending_store_o,

        input  logic [31:0]           vreg_pend_wr_i,
        output logic [31:0]           vreg_pend_rd_o,
        input  logic [31:0]           vreg_pend_rd_i,

        output logic [31:0]           clear_wr_hazards_o,

        input  logic [XIF_ID_CNT-1:0] instr_spec_i,
        input  logic [XIF_ID_CNT-1:0] instr_killed_i,
        output logic                  instr_done_valid_o,
        output logic [XIF_ID_W-1:0]   instr_done_id_o,

        output logic                  trans_complete_valid_o,
        output logic [XIF_ID_W-1:0]   trans_complete_id_o,
        output logic                  trans_complete_exc_o,
        output logic [5:0]            trans_complete_exccode_o,

        // connections to register file:
        input  logic [VREG_W-1:0]     vreg_mask_i,      // content of v0, rearranged as a byte mask
        input  logic [VREG_W-1:0]     vreg_rd_i,
        output logic [4:0]            vreg_rd_addr_o,
        output logic [VREG_W-1:0]     vreg_wr_o,
        output logic [4:0]            vreg_wr_addr_o,
        output logic [VMSK_W-1:0]     vreg_wr_mask_o,
        output logic                  vreg_wr_en_o,

        vproc_xif.coproc_mem          xif_mem_if,
        vproc_xif.coproc_mem_result   xif_memres_if
    );

    import vproc_pkg::*;

    if ((VMEM_W & (VMEM_W - 1)) != 0 || VMEM_W < 32 || VMEM_W >= VREG_W) begin
        $fatal(1, "The vector memory interface width VMEM_W must be at least 32, less than ",
                  "the vector register width VREG_W and a power of two.  ",
                  "The current value of %d is invalid.", VMEM_W);
    end

    if (MAX_WR_ATTEMPTS < 1 || (1 << (MAX_WR_ATTEMPTS - 1)) > VREG_W / VMEM_W) begin
        $fatal(1, "The maximum number of write attempts MAX_WR_ATTEMPTS of a unit ",
                  "must be at least 1 and 2^(MAX_WR_ATTEMPTS-1) must be less than or ",
                  "equal to the ratio of the vector register width vs the operand width ",
                  "of that unit.  ",
                  "For the vector LSU MAX_WR_ATTEMPTS is %d and that ratio is %d.",
                  MAX_WR_ATTEMPTS, VREG_W / VMEM_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (MAX_WR_ATTEMPTS - 1)) - 1;


    ///////////////////////////////////////////////////////////////////////////
    // LSU STATE:

    localparam int unsigned LSU_UNIT_CYCLES_PER_VREG = VREG_W / VMEM_W; // cycles per vreg for unit-stride loads/stores
    localparam int unsigned LSU_UNIT_COUNTER_W       = $clog2(LSU_UNIT_CYCLES_PER_VREG) + 3;

    localparam int unsigned LSU_STRI_MAX_ELEMS_PER_VMEM = VMEM_W / 8; // maximum number of elems read at once for strided/indexed loads
    localparam int unsigned LSU_STRI_COUNTER_EXT_W      = $clog2(LSU_STRI_MAX_ELEMS_PER_VMEM);

    localparam int unsigned LSU_COUNTER_W = LSU_UNIT_COUNTER_W + LSU_STRI_COUNTER_EXT_W;

    typedef union packed {
        logic [LSU_COUNTER_W-1:0] val;
        struct packed {
            logic [2:0]                        mul;
            logic [LSU_UNIT_COUNTER_W-4:0]     unit;
            logic [LSU_STRI_COUNTER_EXT_W-1:0] stri;
        } part;
    } lsu_counter;

    typedef struct packed {
        lsu_counter          count;
        logic                first_cycle;
        logic                last_cycle;
        logic [XIF_ID_W-1:0] id;
        op_mode_lsu          mode;
        cfg_emul             emul;       // effective MUL factor
        logic [CFG_VL_W-1:0] vl;
        logic                vl_0;
        op_regs              rs1;
        op_regs              rs2;
        logic                vs2_fetch;
        logic                vs2_shift;
        logic                v0msk_fetch;
        logic                v0msk_shift;
        logic [4:0]          vd;
        logic                vs3_fetch;
        logic                vs3_shift;
        logic                vd_store;
    } lsu_state;

    // reduced LSU state for passing through the queue
    typedef struct packed {
        lsu_counter          count;
        logic                first_cycle;
        logic                last_cycle;
        logic [XIF_ID_W-1:0] id;
        op_mode_lsu          mode;
        logic [CFG_VL_W-1:0] vl;
        logic                vl_0;
        logic [4:0]          vd;
        logic                vd_store;
        logic                exc;
        logic [5:0]          exccode;
    } lsu_state_red;

    // LSU STATES:
    // the LSU has 5 states that keep track of the states of the various
    // pipeline stages:
    //  - init: Initial stage, reads vs2 for indexed accesses
    //  - addr: Addressing stage, generates the memory address
    //  - req:  Request stage, requests the memory access (also provides write data for stores)
    //  - data: Read data stage, receives read data (only used for loads)
    //  - wb:   Register write-back stage, writes memory data to vreg (only used for loads)
    // 'init' and 'data' are primary stages, that are initialized when a load/store is initiated.
    // 'addr' and 'req' are derived from 'init' (see pipeline buffers).
    // 'wb' is derived from 'data' (see pipeline buffers).
    // Initializing 'data' at the start instead of deriving it from e.g. 'req' allows memory requests
    // to continue while still waiting for read data (for memories that are capable of pipelining loads).

    logic        state_valid_q,  state_valid_d;
    lsu_state    state_q,        state_d;        // addressing state
    logic [31:0] vreg_pend_wr_q, vreg_pend_wr_d; // local copy of global vreg write mask
    always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_lsu_state_valid
        if (~async_rst_ni) begin
            state_valid_q <= 1'b0;
        end
        else if (~sync_rst_ni) begin
            state_valid_q <= 1'b0;
        end else begin
            state_valid_q <= state_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_lsu_state
        state_q        <= state_d;
        vreg_pend_wr_q <= vreg_pend_wr_d;
    end

    logic last_cycle;
    always_comb begin
        last_cycle = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (state_q.emul)
            EMUL_1: last_cycle = state_q.count.val[LSU_COUNTER_W-4:0] == '1;
            EMUL_2: last_cycle = state_q.count.val[LSU_COUNTER_W-3:0] == '1;
            EMUL_4: last_cycle = state_q.count.val[LSU_COUNTER_W-2:0] == '1;
            EMUL_8: last_cycle = state_q.count.val[LSU_COUNTER_W-1:0] == '1;
            default: ;
        endcase
    end

    logic pipeline_ready;
    always_comb begin
        op_ack_o       = 1'b0;
        misaligned_o   = 1'b0;
        state_valid_d  = state_valid_q;
        state_d        = state_q;
        vreg_pend_wr_d = vreg_pend_wr_q & vreg_pend_wr_i;

        if (((~state_valid_q) | (last_cycle & pipeline_ready)) & op_rdy_i) begin
            op_ack_o     = 1'b1;
            misaligned_o = (rs1_i.r.xval[$clog2(VMEM_W/8)-1:0] != '0); // |
                           //((mode_q.stride == LSU_STRIDED) & (rs2_i.r.xval[]));
            state_d.count.val = '0;
            if (mode_i.stride == LSU_UNITSTRIDE) begin
                state_d.count.part.stri = '1;
            end else begin
                unique case (mode_i.eew)
                    VSEW_16: begin
                        state_d.count.part.stri = 1;
                    end
                    VSEW_32: begin
                        state_d.count.part.stri = 3;
                    end
                    default: ;
                endcase
            end
            state_valid_d       = 1'b1;
            state_d.first_cycle = 1'b1;
            state_d.id          = id_i;
            state_d.mode        = mode_i;
            state_d.emul        = emul_i;
            state_d.vl          = vl_i;
            state_d.vl_0        = vl_0_i;
            state_d.rs1         = rs1_i;
            state_d.rs2         = rs2_i;
            state_d.vs2_fetch   = rs2_i.vreg;
            state_d.vs2_shift   = 1'b1;
            state_d.v0msk_fetch = 1'b1;
            state_d.v0msk_shift = 1'b1;
            state_d.vd          = vd_i;
            state_d.vs3_fetch   = mode_i.store;
            state_d.vs3_shift   = 1'b1;
            state_d.vd_store    = 1'b0;
            vreg_pend_wr_d      = vreg_pend_wr_i;
        end else begin
            // advance address if load/store has been granted:
            if (state_valid_q & pipeline_ready) begin
                if (state_q.mode.stride == LSU_UNITSTRIDE) begin
                    state_d.count.val = state_q.count.val + (1 << LSU_STRI_COUNTER_EXT_W);
                end else begin
                    unique case (state_q.mode.eew)
                        VSEW_8:  state_d.count.val = state_q.count.val + 1;
                        VSEW_16: state_d.count.val = state_q.count.val + 2;
                        VSEW_32: state_d.count.val = state_q.count.val + 4;
                        default: ;
                    endcase
                end
                state_valid_d       = ~last_cycle;
                state_d.first_cycle = 1'b0;
                unique case (state_q.mode.stride)
                    LSU_UNITSTRIDE: state_d.rs1.r.xval = state_q.rs1.r.xval + (VMEM_W / 8);
                    LSU_STRIDED:    state_d.rs1.r.xval = state_q.rs1.r.xval + state_q.rs2.r.xval;
                    default: ; // for indexed loads the base address stays the same
                endcase
                state_d.vs2_fetch = 1'b0;
                state_d.vs3_fetch = 1'b0;
                if (state_q.count.val[LSU_COUNTER_W-4:0] == '1) begin
                    if (state_q.rs2.vreg) begin
                        state_d.rs2.r.vaddr[2:0] = state_q.rs2.r.vaddr[2:0] + 3'b1;
                        state_d.vs2_fetch        = state_q.rs2.vreg;
                    end
                    state_d.vd[2:0]   = state_q.vd[2:0] + 3'b1;
                    state_d.vs3_fetch = state_q.mode.store;
                end
                unique case (state_q.mode.eew)
                    VSEW_8:  state_d.vs2_shift = state_q.count.val[1:0] == '1;
                    VSEW_16: state_d.vs2_shift = state_q.count.val[1  ];
                    VSEW_32: state_d.vs2_shift = 1'b1;
                    default: ;
                endcase
                state_d.vs3_shift = (state_q.count.part.stri == '1) | (state_q.mode.stride == LSU_UNITSTRIDE);
                state_d.v0msk_fetch = 1'b0;
                unique case (state_q.mode.eew)
                    VSEW_8:  state_d.v0msk_shift = 1'b1;
                    VSEW_16: state_d.v0msk_shift = state_q.count.val[                         LSU_STRI_COUNTER_EXT_W];
                    VSEW_32: state_d.v0msk_shift = state_q.count.val[LSU_STRI_COUNTER_EXT_W+1:LSU_STRI_COUNTER_EXT_W] == '1;
                    default: ;
                endcase
                if ((state_q.mode.stride != LSU_UNITSTRIDE) & (state_q.count.val[LSU_STRI_COUNTER_EXT_W-1:0] != '1)) begin
                    state_d.v0msk_shift = 1'b0;
                end
            end
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // LSU PIPELINE BUFFERS:

    // pass state information along pipeline:
    logic                           state_req_ready,   lsu_queue_ready;
    logic         state_init_stall, state_req_stall;
    logic         state_init_valid, state_req_valid_q, state_req_valid_d, state_rdata_valid_q;
    lsu_state     state_init,       state_req_q,       state_req_d;
    lsu_state_red state_rdata_d,                                          state_rdata_q;
    always_comb begin
        state_init_valid      = state_valid_q;
        state_init            = state_q;
        state_init.last_cycle = state_valid_q & last_cycle;
        state_init.vd_store   = state_q.count.val[LSU_COUNTER_W-4:0] == '1;
    end
    logic unpack_ready;
    assign pipeline_ready = unpack_ready & ~state_init_stall;

    lsu_state unpack_flags_any, unpack_flags_all;
    assign pending_load_o  = (state_init_valid  & ~state_init.mode.store      ) |
                             (                    ~unpack_flags_all.mode.store) |
                             (state_req_valid_q & ~state_req_q.mode.store     );
    assign pending_store_o = (state_init_valid  &  state_init.mode.store      ) |
                             (                     unpack_flags_any.mode.store) |
                             (state_req_valid_q &  state_req_q.mode.store     );

    // request address:
    logic [31:0] req_addr_q, req_addr_d;

    // store data and mask buffers:
    logic [VMEM_W  -1:0] wdata_buf_q, wdata_buf_d;
    logic [VMEM_W/8-1:0] wmask_buf_q, wmask_buf_d;

    // temporary buffer for byte mask during request:
    logic [VMEM_W/8-1:0] vmsk_tmp_q, vmsk_tmp_d;

    // memory request caused an exception:
    logic mem_exc_q, mem_exc_d;

    // memory request caused an error (exception or bus error):
    logic       mem_err_q,     mem_err_d;
    logic [5:0] mem_exccode_q, mem_exccode_d;

    // load data, offset and mask buffers:
    logic [       VMEM_W   -1:0] rdata_buf_q, rdata_buf_d;
    logic [$clog2(VMEM_W/8)-1:0] rdata_off_q, rdata_off_d;
    logic [       VMEM_W/8 -1:0] rmask_buf_q, rmask_buf_d;

    generate
        if (BUF_REQUEST) begin
             always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_lsu_stage_req_valid
                if (~async_rst_ni) begin
                    state_req_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_req_valid_q <= 1'b0;
                end
                else if (state_req_ready) begin
                    state_req_valid_q <= state_req_valid_d;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_lsu_stage_req
                if (state_req_ready & state_req_valid_d) begin
                    state_req_q <= state_req_d;
                    req_addr_q  <= req_addr_d;
                    wdata_buf_q <= wdata_buf_d;
                    wmask_buf_q <= wmask_buf_d;
                    vmsk_tmp_q  <= vmsk_tmp_d;
                    mem_exc_q   <= mem_exc_d;
                end
            end
            assign state_req_ready = ~state_req_valid_q | (xif_mem_if.mem_valid & xif_mem_if.mem_ready) | (~state_req_stall & ~xif_mem_if.mem_valid);
        end else begin
            always_comb begin
                state_req_valid_q = state_req_valid_d;
                state_req_q       = state_req_d;
                req_addr_q        = req_addr_d;
                wdata_buf_q       = wdata_buf_d;
                wmask_buf_q       = wmask_buf_d;
                vmsk_tmp_q        = vmsk_tmp_d;
            end
            always_ff @(posedge clk_i) begin
                // always need a flip-flop for the exception flag
                mem_exc_q <= mem_exc_d;
            end
            assign state_req_ready = (xif_mem_if.mem_valid & xif_mem_if.mem_ready) | (~state_req_stall & ~xif_mem_if.mem_valid);
        end

        // Note: The stages receiving memory data and writing it to vector
        // registers cannot stall, since there is no way to pause memory read
        // data once the memory requests have been issued.  Therefore, any
        // checks which might stall the pipeline (destination vector register
        // available, instruction committed) must be done *before* generating
        // the memory requests.
        if (BUF_RDATA) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_lsu_stage_rdata_valid
                if (~async_rst_ni) begin
                    state_rdata_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_rdata_valid_q <= 1'b0;
                end
                else begin
                    state_rdata_valid_q <= xif_memres_if.mem_result_valid & ~state_rdata_d.mode.store;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_lsu_stage_rdata
                if (xif_memres_if.mem_result_valid) begin
                    state_rdata_q <= state_rdata_d;
                    rdata_buf_q   <= rdata_buf_d;
                    rdata_off_q   <= rdata_off_d;
                    rmask_buf_q   <= rmask_buf_d;
                    mem_err_q     <= mem_err_d;
                    mem_exccode_q <= mem_exccode_d;
                end
            end
        end else begin
            always_comb begin
                state_rdata_valid_q = xif_memres_if.mem_result_valid & ~state_rdata_d.mode.store;
                state_rdata_q       = state_rdata_d;
                rdata_buf_q         = rdata_buf_d;
                rdata_off_q         = rdata_off_d;
                rmask_buf_q         = rmask_buf_d;
            end
            always_ff @(posedge clk_i) begin
                // always need a flip-flop for the error flag and exception code
                mem_err_q     <= mem_err_d;
                mem_exccode_q <= mem_exccode_d;
            end
        end
    endgenerate

    // Stall vreg reads until pending writes are complete; note that vreg read
    // stalling always happens in the init stage, since otherwise a substantial
    // amount of state would have to be forwarded (such as vreg_pend_wr_q)
    assign state_init_stall = (state_init.vs2_fetch   & vreg_pend_wr_q[state_init.rs2.r.vaddr]) |
                              (state_init.vs3_fetch   & vreg_pend_wr_q[state_init.vd         ]) |
                              (state_init.v0msk_fetch & state_init.mode.masked & vreg_pend_wr_q[0]);

    // Stall vreg writes until pending reads of the destination register are
    // complete and while the instruction is speculative; for the LSU stalling
    // has to happen at the request stage, since later stalling is not possible
    assign state_req_stall = (~state_req_q.mode.store & state_req_q.vd_store & vreg_pend_rd_i[state_req_q.vd]) | instr_spec_i[state_req_q.id] | ~lsu_queue_ready;

    assign instr_done_valid_o = state_req_valid_q & state_req_q.last_cycle & xif_mem_if.mem_valid & xif_mem_if.mem_ready;
    assign instr_done_id_o    = state_req_q.id;

    // pending vreg reads
    // Note: The pipeline might stall while reading a vreg, hence a vreg has to
    // be part of the pending reads until the read is complete.
    logic [31:0] pend_vs2, pend_vs3;
    always_comb begin
        pend_vs2 = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_init.emul)
            EMUL_1: pend_vs2 = {31'b0, state_init.vs2_fetch} << state_init.rs2.r.vaddr;
            EMUL_2: pend_vs2 = (32'h03 & ((32'h02 | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs2.r.vaddr[4:1], 1'b0};
            EMUL_4: pend_vs2 = (32'h0F & ((32'h0E | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs2.r.vaddr[4:2], 2'b0};
            EMUL_8: pend_vs2 = (32'hFF & ((32'hFE | {31'b0, state_init.vs2_fetch}) << state_init.count.part.mul[2:0])) << {state_init.rs2.r.vaddr[4:3], 3'b0};
            default: ;
        endcase
        pend_vs3 = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_init.emul)
            EMUL_1: pend_vs3 = {31'b0, state_init.vs3_fetch} << state_init.vd;
            EMUL_2: pend_vs3 = (32'h03 & ((32'h02 | {31'b0, state_init.vs3_fetch}) << state_init.count.part.mul[2:0])) << {state_init.vd[4:1], 1'b0};
            EMUL_4: pend_vs3 = (32'h0F & ((32'h0E | {31'b0, state_init.vs3_fetch}) << state_init.count.part.mul[2:0])) << {state_init.vd[4:2], 2'b0};
            EMUL_8: pend_vs3 = (32'hFF & ((32'hFE | {31'b0, state_init.vs3_fetch}) << state_init.count.part.mul[2:0])) << {state_init.vd[4:3], 3'b0};
            default: ;
        endcase
    end
    // Note: vs3 is read in the second cycle; the v0 mask has no extra buffer
    // and is always read in state_vs2
    logic [31:0] unpack_pend_rd;
    assign vreg_pend_rd_o = ((
            ((state_init_valid & state_init.rs2.vreg   ) ? pend_vs2                        : '0) |
            ((state_init_valid & state_init.mode.store ) ? pend_vs3                        : '0) |
            ((state_init_valid & state_init.v0msk_fetch) ? {31'b0, state_init.mode.masked} : '0)
        ) & ~vreg_pend_wr_q) |
    unpack_pend_rd;


    ///////////////////////////////////////////////////////////////////////////
    // LSU READ/WRITE:

    logic        [2:0]       unpack_op_load;
    logic        [2:0][4 :0] unpack_op_vaddr;
    unpack_flags [2:0]       unpack_op_flags;
    logic        [2:0][31:0] unpack_op_xval;
    always_comb begin
        unpack_op_flags  [0]          = unpack_flags'('0);
        unpack_op_flags  [0].shift    = state_init.vs2_shift;
        unpack_op_load   [0]          = state_init.vs2_fetch;
        unpack_op_flags  [0].elemwise = '0;
        unpack_op_vaddr  [0]          = state_init.rs2.r.vaddr;
        unpack_op_xval   [0]          = '0;
        unpack_op_flags  [1]          = unpack_flags'('0);
        unpack_op_flags  [1].shift    = state_init.vs3_shift;
        unpack_op_load   [1]          = state_init.vs3_fetch;
        unpack_op_flags  [1].elemwise = '0;
        unpack_op_vaddr  [1]          = state_init.vd;
        unpack_op_xval   [1]          = '0;
        unpack_op_flags  [2]          = unpack_flags'('0);
        unpack_op_flags  [2].shift    = state_init.v0msk_shift;
        unpack_op_load   [2]          = state_init.v0msk_fetch & state_init.mode.masked;
        unpack_op_flags  [2].elemwise = state_init.mode.stride != LSU_UNITSTRIDE;
        unpack_op_vaddr  [2]          = '0;
        unpack_op_xval   [2]          = '0;
    end

    localparam int unsigned UNPACK_VPORT_W [2] = '{VREG_W,VREG_W};
    localparam int unsigned UNPACK_VADDR_W [2] = '{5,5};
    localparam int unsigned UNPACK_OP_W    [3] = '{32,VMEM_W,VMEM_W/8};
    localparam int unsigned UNPACK_OP_STAGE[3] = '{1,2,2};
    localparam int unsigned UNPACK_OP_SRC  [3] = '{0,0,1};

    logic [2:0][VMEM_W-1:0] unpack_ops;
    logic [1:0][4:0]        unpack_vreg_addr;
    logic [1:0][VREG_W-1:0] unpack_vreg_data;
    vproc_vregunpack #(
        .MAX_VPORT_W          ( VREG_W                               ),
        .MAX_VADDR_W          ( 5                                    ),
        .VPORT_CNT            ( 2                                    ),
        .VPORT_W              ( UNPACK_VPORT_W                       ),
        .VADDR_W              ( UNPACK_VADDR_W                       ),
        .VPORT_ADDR_ZERO      ( 2'b10                                ),
        .VPORT_BUFFER         ( 2'b01                                ),
        .MAX_OP_W             ( VMEM_W                               ),
        .OP_CNT               ( 3                                    ),
        .OP_W                 ( UNPACK_OP_W                          ),
        .OP_STAGE             ( UNPACK_OP_STAGE                      ),
        .OP_SRC               ( UNPACK_OP_SRC                        ),
        .OP_ADDR_OFFSET_OP0   ( 3'b000                               ),
        .OP_MASK              ( 3'b100                               ),
        .OP_XREG              ( 3'b000                               ),
        .OP_NARROW            ( 3'b000                               ),
        .OP_ALLOW_ELEMWISE    ( 3'b110                               ),
        .OP_ALWAYS_ELEMWISE   ( 3'b001                               ),
        .OP_HOLD_FLAG         ( 3'b000                               ),
        .UNPACK_STAGES        ( 3                                    ),
        .FLAGS_T              ( unpack_flags                         ),
        .CTRL_DATA_W          ( $bits(lsu_state)                     ),
        .DONT_CARE_ZERO       ( DONT_CARE_ZERO                       )
    ) lsu_unpack (
        .clk_i                ( clk_i                                ),
        .async_rst_ni         ( async_rst_ni                         ),
        .sync_rst_ni          ( sync_rst_ni                          ),
        .vreg_rd_addr_o       ( unpack_vreg_addr                     ),
        .vreg_rd_data_i       ( unpack_vreg_data                     ),
        .pipe_in_valid_i      ( state_init_valid & ~state_init_stall ),
        .pipe_in_ready_o      ( unpack_ready                         ),
        .pipe_in_ctrl_i       ( state_init                           ),
        .pipe_in_eew_i        ( state_init.mode.eew                  ),
        .pipe_in_op_load_i    ( unpack_op_load                       ),
        .pipe_in_op_vaddr_i   ( unpack_op_vaddr                      ),
        .pipe_in_op_flags_i   ( unpack_op_flags                      ),
        .pipe_in_op_xval_i    ( unpack_op_xval                       ),
        .pipe_out_valid_o     ( state_req_valid_d                    ),
        .pipe_out_ready_i     ( state_req_ready                      ),
        .pipe_out_ctrl_o      ( state_req_d                          ),
        .pipe_out_op_data_o   ( unpack_ops                           ),
        .pending_vreg_reads_o ( unpack_pend_rd                       ),
        .stage_valid_any_o    (                                      ),
        .ctrl_flags_any_o     ( unpack_flags_any                     ),
        .ctrl_flags_all_o     ( unpack_flags_all                     )
    );
    assign vreg_rd_addr_o = unpack_vreg_addr[0];
    always_comb begin
        unpack_vreg_data[0] = vreg_rd_i;
        unpack_vreg_data[1] = vreg_mask_i;
    end
    logic [31        :0] vs2_data;
    logic [VMEM_W  -1:0] vs3_data;
    logic [VMEM_W/8-1:0] vmsk_data;
    assign vs2_data  = unpack_ops[0][31:0];
    assign vs3_data  = unpack_ops[1];
    assign vmsk_data = unpack_ops[2][VMEM_W/8-1:0];

    // compose memory address:
    always_comb begin
        req_addr_d = state_req_d.rs1.r.xval;
        if (state_req_d.mode.stride == LSU_INDEXED) begin
            req_addr_d = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_req_d.mode.eew)
                VSEW_8:  req_addr_d = state_req_d.rs1.r.xval + {24'b0, vs2_data[7 :0]};
                VSEW_16: req_addr_d = state_req_d.rs1.r.xval + {16'b0, vs2_data[15:0]};
                VSEW_32: req_addr_d = state_req_d.rs1.r.xval +         vs2_data[31:0] ;
                default: ;
            endcase
        end
    end

    assign vmsk_tmp_d = vmsk_data;

    // write data conversion and masking:
    logic [VREG_W-1:0] wdata_unit_vl_mask;
    logic              wdata_stri_mask;
    assign wdata_unit_vl_mask =   state_req_d.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_req_d.vl));
    assign wdata_stri_mask    = (~state_req_d.vl_0 & (state_req_d.count.val <= state_req_d.vl)) & (state_req_d.mode.masked ? vmsk_data[0] : 1'b1);
    always_comb begin
        wdata_buf_d = DONT_CARE_ZERO ? '0 : 'x;
        wmask_buf_d = DONT_CARE_ZERO ? '0 : 'x;
        if (state_req_d.mode.stride == LSU_UNITSTRIDE) begin
            wdata_buf_d = vs3_data[VMEM_W-1:0];
            wmask_buf_d = (state_req_d.mode.masked ? vmsk_data : '1) & wdata_unit_vl_mask[state_req_d.count.val[LSU_COUNTER_W-1:LSU_STRI_COUNTER_EXT_W]*VMEM_W/8 +: VMEM_W/8];
        end else begin
            unique case (state_req_d.mode.eew)
                VSEW_8: begin
                    for (int i = 0; i < VMEM_W / 8 ; i++)
                        wdata_buf_d[i*8  +: 8 ] = vs3_data[7 :0];
                    wmask_buf_d = {{VMEM_W/8-1{1'b0}},    wdata_stri_mask  } <<  req_addr_d[$clog2(VMEM_W/8)-1:0]                                    ;
                end
                VSEW_16: begin
                    for (int i = 0; i < VMEM_W / 16; i++)
                        wdata_buf_d[i*16 +: 16] = vs3_data[15:0];
                    wmask_buf_d = {{VMEM_W/8-2{1'b0}}, {2{wdata_stri_mask}}} << (req_addr_d[$clog2(VMEM_W/8)-1:0] & ({$clog2(VMEM_W/8){1'b1}} << 1));
                end
                VSEW_32: begin
                    for (int i = 0; i < VMEM_W / 32; i++)
                        wdata_buf_d[i*32 +: 32] = vs3_data[31:0];
                    wmask_buf_d = {{VMEM_W/8-4{1'b0}}, {4{wdata_stri_mask}}} << (req_addr_d[$clog2(VMEM_W/8)-1:0] & ({$clog2(VMEM_W/8){1'b1}} << 2));
                end
                default: ;
            endcase
        end
    end

    // memory request (keep requesting next access while addressing is not complete)
    assign xif_mem_if.mem_valid     = state_req_valid_q & ~state_req_stall & ~instr_killed_i[state_req_q.id] & (~mem_exc_q | state_req_q.first_cycle);
    assign xif_mem_if.mem_req.id    = state_req_q.id;
    assign xif_mem_if.mem_req.addr  = {req_addr_q[31:$clog2(VMEM_W/8)], {$clog2(VMEM_W/8){1'b0}}};
    assign xif_mem_if.mem_req.mode  = '0;
    assign xif_mem_if.mem_req.we    = state_req_q.mode.store;
    assign xif_mem_if.mem_req.be    = wmask_buf_q;
    assign xif_mem_if.mem_req.wdata = wdata_buf_q;
    assign xif_mem_if.mem_req.last  = state_req_q.last_cycle;
    assign xif_mem_if.mem_req.spec  = '0;

    // monitor the memory response for exceptions
    always_comb begin
        mem_exc_d = mem_exc_q;
        if (state_req_q.first_cycle | ~mem_exc_q) begin
            // reset the exception flag in the first cycle, unless there is an
            // exception
            mem_exc_d = xif_mem_if.mem_valid & xif_mem_if.mem_ready & xif_mem_if.mem_resp.exc;
        end
    end

    // queue for storing masks and offsets until the memory system fulfills the request:
    lsu_state_red state_req_red;
    always_comb begin
        state_req_red             = DONT_CARE_ZERO ? '0 : 'x;
        state_req_red.count       = state_req_q.count;
        state_req_red.first_cycle = state_req_q.first_cycle;
        state_req_red.last_cycle  = state_req_q.last_cycle;
        state_req_red.id          = state_req_q.id;
        state_req_red.mode        = state_req_q.mode;
        state_req_red.vl          = state_req_q.vl;
        state_req_red.vl_0        = state_req_q.vl_0;
        state_req_red.vd          = state_req_q.vd;
        state_req_red.vd_store    = state_req_q.vd_store;
        state_req_red.exc         = xif_mem_if.mem_resp.exc;
        state_req_red.exccode     = xif_mem_if.mem_resp.exccode;
    end
    logic         deq_valid; // LSU queue dequeue valid signal
    lsu_state_red deq_state;
    vproc_queue #(
        .WIDTH        ( $clog2(VMEM_W/8) + VMEM_W/8 + $bits(lsu_state_red)            ),
        .DEPTH        ( 4                                                             )
    ) lsu_queue (
        .clk_i        ( clk_i                                                         ),
        .async_rst_ni ( async_rst_ni                                                  ),
        .sync_rst_ni  ( sync_rst_ni                                                   ),
        .enq_ready_o  ( lsu_queue_ready                                               ),
        .enq_valid_i  ( state_req_valid_q & state_req_ready                           ),
        .enq_data_i   ( {req_addr_q[$clog2(VMEM_W/8)-1:0], vmsk_tmp_q, state_req_red} ),
        .deq_ready_i  ( xif_memres_if.mem_result_valid | mem_err_d                    ),
        .deq_valid_o  ( deq_valid                                                     ),
        .deq_data_o   ( {rdata_off_d, rmask_buf_d, deq_state}                         ),
        .flags_any_o  (                                                               ),
        .flags_all_o  (                                                               )
    );

    // monitor the memory result for bus errors and the queue for exceptions
    always_comb begin
        mem_err_d     = mem_err_q;
        mem_exccode_d = mem_exccode_q;
        if ((deq_valid & deq_state.first_cycle) | ~mem_err_q) begin
            // reset the error flag in the first cycle, unless there is a bus
            // error or an exception occured during the request
            mem_err_d     = deq_state.exc | (xif_memres_if.mem_result_valid & xif_memres_if.mem_result.err);
            mem_exccode_d = deq_state.exc ? deq_state.exccode : (
                // bus error translates to a load/store access fault exception
                deq_state.mode.store ? 6'h07 : 6'h05
            );
        end
    end

    // LSU result (indicates potential exceptions):
    assign trans_complete_valid_o   = deq_valid & deq_state.last_cycle & (xif_memres_if.mem_result_valid | mem_err_d);
    assign trans_complete_id_o      = deq_state.id;
    assign trans_complete_exc_o     = mem_err_d;
    assign trans_complete_exccode_o = mem_exccode_d;

    // load data state
    always_comb begin
        state_rdata_d     = deq_state;
        state_rdata_d.exc = mem_err_d;
    end

    // load data:
    assign rdata_buf_d = xif_memres_if.mem_result.rdata;

    // load data conversion:
    logic [VREG_W  -1:0] rdata_unit_vl_mask;
    logic [VMEM_W/8-1:0] rdata_unit_vdmsk;
    assign rdata_unit_vl_mask = state_rdata_q.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_rdata_q.vl));
    assign rdata_unit_vdmsk   = (state_rdata_q.mode.masked ? rmask_buf_q : {VMEM_W/8{1'b1}}) & rdata_unit_vl_mask[state_rdata_q.count.val[LSU_COUNTER_W-1:LSU_STRI_COUNTER_EXT_W]*VMEM_W/8 +: VMEM_W/8];
    logic rdata_stri_vdmsk;
    assign rdata_stri_vdmsk = (~state_rdata_q.vl_0 & (state_rdata_q.count.val <= state_rdata_q.vl)) & (state_rdata_q.mode.masked ? rmask_buf_q[0] : 1'b1);

    logic      [0:0] pack_res_store, pack_res_valid;
    pack_flags [0:0] pack_res_flags;
    always_comb begin
        pack_res_flags[0] = pack_flags'('0);
        pack_res_store[0] = state_rdata_q.vd_store & ~state_rdata_q.exc;
        pack_res_valid[0] = state_rdata_valid_q;
        if (state_rdata_q.mode.stride == LSU_UNITSTRIDE) begin
            pack_res_flags[0].shift    = 1'b1;
            pack_res_flags[0].elemwise = 1'b0;
        end else begin
            pack_res_flags[0].shift = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_rdata_q.mode.eew)
                VSEW_8:  pack_res_flags[0].shift =  state_rdata_q.count.part.stri       == '0;
                VSEW_16: pack_res_flags[0].shift = (state_rdata_q.count.part.stri >> 1) == '0;
                VSEW_32: pack_res_flags[0].shift = (state_rdata_q.count.part.stri >> 2) == '0;
                default: ;
            endcase
            pack_res_flags[0].elemwise = 1'b1;
        end
    end
    logic [0:0][VMEM_W-1:0] pack_res_data, pack_res_mask;
    always_comb begin
        if (state_rdata_q.mode.stride == LSU_UNITSTRIDE) begin
            pack_res_data[0] = rdata_buf_q;
        end else begin
            pack_res_data[0] = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_rdata_q.mode.eew)
                VSEW_8:  pack_res_data[0][7 :0] = rdata_buf_q[{3'b000, rdata_off_q                                  } * 8 +: 8 ];
                VSEW_16: pack_res_data[0][15:0] = rdata_buf_q[{3'b000, rdata_off_q & ({$clog2(VMEM_W/8){1'b1}} << 1)} * 8 +: 16];
                VSEW_32: pack_res_data[0][31:0] = rdata_buf_q[{3'b000, rdata_off_q & ({$clog2(VMEM_W/8){1'b1}} << 2)} * 8 +: 32];
                default: ;
            endcase
        end
        pack_res_mask                  = '0;
        pack_res_mask[0][VMEM_W/8-1:0] = (state_rdata_q.mode.stride == LSU_UNITSTRIDE) ? rdata_unit_vdmsk : {(VMEM_W/8){rdata_stri_vdmsk}};
    end
    localparam int unsigned PACK_RES_W[1] = '{VMEM_W};
    vproc_vregpack #(
        .VPORT_W                     ( VREG_W                   ),
        .VADDR_W                     ( 5                        ),
        .VPORT_WR_ATTEMPTS           ( MAX_WR_ATTEMPTS          ),
        .VPORT_PEND_CLR_BULK         ( '0                       ),
        .MAX_RES_W                   ( VMEM_W                   ),
        .RES_CNT                     ( 1                        ),
        .RES_W                       ( PACK_RES_W               ),
        .RES_MASK                    ( '0                       ),
        .RES_XREG                    ( '0                       ),
        .RES_NARROW                  ( '0                       ),
        .RES_ALLOW_ELEMWISE          ( 1'b1                     ),
        .RES_ALWAYS_ELEMWISE         ( '0                       ),
        .FLAGS_T                     ( pack_flags               ),
        .INSTR_ID_W                  ( XIF_ID_W                 ),
        .INSTR_ID_CNT                ( XIF_ID_CNT               ),
        .DONT_CARE_ZERO              ( DONT_CARE_ZERO           )
    ) lsu_pack (
        .clk_i                       ( clk_i                    ),
        .async_rst_ni                ( async_rst_ni             ),
        .sync_rst_ni                 ( sync_rst_ni              ),
        .pipe_in_valid_i             ( state_rdata_valid_q      ),
        .pipe_in_ready_o             (                          ),
        .pipe_in_instr_id_i          ( state_rdata_q.id         ),
        .pipe_in_eew_i               ( state_rdata_q.mode.eew   ),
        .pipe_in_vaddr_i             ( state_rdata_q.vd         ),
        .pipe_in_res_store_i         ( pack_res_store           ),
        .pipe_in_res_valid_i         ( pack_res_valid           ),
        .pipe_in_res_flags_i         ( pack_res_flags           ),
        .pipe_in_res_data_i          ( pack_res_data            ),
        .pipe_in_res_mask_i          ( pack_res_mask            ),
        .pipe_in_pend_clr_i          ( state_rdata_q.vd_store   ),
        .pipe_in_pend_clr_cnt_i      ( '0                       ),
        .pipe_in_instr_done_i        ( state_rdata_q.last_cycle ),
        .vreg_wr_valid_o             ( vreg_wr_en_o             ),
        .vreg_wr_ready_i             ( 1'b1                     ),
        .vreg_wr_addr_o              ( vreg_wr_addr_o           ),
        .vreg_wr_be_o                ( vreg_wr_mask_o           ),
        .vreg_wr_data_o              ( vreg_wr_o                ),
        .pending_vreg_reads_i        ( '0                       ),
        .clear_pending_vreg_writes_o ( clear_wr_hazards_o       ),
        .instr_spec_i                ( '0                       ),
        .instr_killed_i              ( '0                       ),
        .instr_done_valid_o          (                          ),
        .instr_done_id_o             (                          )
    );


`ifdef VPROC_SVA
`include "vproc_lsu_sva.svh"
`endif

endmodule
