// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


`include "vproc_vregshift.svh"

module vproc_lsu #(
        parameter int unsigned        VREG_W          = 128,  // width in bits of vector registers
        parameter int unsigned        VMSK_W          = 16,   // width of vector register masks (= VREG_W / 8)
        parameter int unsigned        VMEM_W          = 32,   // width in bits of the vector memory interface
        parameter int unsigned        CFG_VL_W        = 7,    // width of VL reg in bits (= log2(VREG_W))
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

        input  vproc_pkg::cfg_vsew    vsew_i,
        input  vproc_pkg::cfg_lmul    lmul_i,
        input  logic [CFG_VL_W-1:0]   vl_i,
        input  logic                  vl_0_i,

        input  logic                  op_rdy_i,
        output logic                  op_ack_o,
        output logic                  misaligned_o,

        input  vproc_pkg::op_mode_lsu mode_i,
        input  logic [31:0]           rs1_val_i,
        input  vproc_pkg::op_regs     rs2_i,
        input  logic [4:0]            vd_i,

        output logic                  pending_load_o,
        output logic                  pending_store_o,

        output logic [31:0]           clear_rd_hazards_o,
        output logic [31:0]           clear_wr_hazards_o,

        // connections to register file:
        input  logic [VREG_W-1:0]     vreg_mask_i,      // content of v0, rearranged as a byte mask
        input  logic [VREG_W-1:0]     vreg_rd_i,
        output logic [4:0]            vreg_rd_addr_o,
        output logic [VREG_W-1:0]     vreg_wr_o,
        output logic [4:0]            vreg_wr_addr_o,
        output logic [VMSK_W-1:0]     vreg_wr_mask_o,
        output logic                  vreg_wr_en_o,

        // connections to memory:
        input  logic                  data_gnt_i,
        input  logic                  data_rvalid_i,
        input  logic                  data_err_i,
        input  logic [VMEM_W-1:0]     data_rdata_i,
        output logic                  data_req_o,
        output logic [31:0]           data_addr_o,
        output logic                  data_we_o,        // write enable
        output logic [(VMEM_W/8)-1:0] data_be_o,        // byte enable
        output logic [VMEM_W-1:0]     data_wdata_o
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
        op_mode_lsu          mode;
        cfg_emul             emul;       // effective MUL factor
        logic [CFG_VL_W-1:0] vl;
        logic                vl_0;
        logic [31:0]         base_addr;
        op_regs              rs2;
        logic                vs2_fetch;
        logic                vs2_shift;
        logic [4:0]          vd;
        logic                vs3_fetch;
        logic                vs3_shift;
        logic                vd_store;
    } lsu_state;

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

    logic     state_valid_q,  state_valid_d;
    lsu_state state_q,        state_d;        // addressing state
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

    cfg_emul            emul;
    logic[CFG_VL_W-1:0] vl;
    always_comb begin
        emul = DONT_CARE_ZERO ? cfg_emul'('0) : cfg_emul'('x);
        vl   = DONT_CARE_ZERO ? '0 : 'x;
        unique case ({mode_i.eew, vsew_i})
            {VSEW_8 , VSEW_32}: begin   // EEW / SEW = 1 / 4
                emul = (lmul_i == LMUL_8) ? EMUL_2 : EMUL_1; // use EMUL == 1 for fractional EMUL (LMUL < 4), vl is updated anyways
                vl   = {2'b00, vl_i[CFG_VL_W-1:2]};
            end
            {VSEW_8 , VSEW_16},
            {VSEW_16, VSEW_32}: begin   // EEW / SEW = 1 / 2
                emul = (lmul_i == LMUL_8) ? EMUL_4 : ((lmul_i == LMUL_4) ? EMUL_2 : EMUL_1);
                vl   = {1'b0, vl_i[CFG_VL_W-1:1]};
            end
            {VSEW_8 , VSEW_8 },
            {VSEW_16, VSEW_16},
            {VSEW_32, VSEW_32}: begin   // EEW / SEW = 1
                unique case (lmul_i)
                    LMUL_F8,
                    LMUL_F4,
                    LMUL_F2,
                    LMUL_1:  emul = EMUL_1;
                    LMUL_2:  emul = EMUL_2;
                    LMUL_4:  emul = EMUL_4;
                    LMUL_8:  emul = EMUL_8;
                    default: ;
                endcase
                vl   = vl_i;
            end
            {VSEW_16, VSEW_8 },
            {VSEW_32, VSEW_16}: begin   // EEW / SEW = 2
                unique case (lmul_i)
                    LMUL_F8,
                    LMUL_F4,
                    LMUL_F2: emul = EMUL_1;
                    LMUL_1:  emul = EMUL_2;
                    LMUL_2:  emul = EMUL_4;
                    LMUL_4:  emul = EMUL_8;
                    default: ;
                endcase
                vl   = {vl_i[CFG_VL_W-2:0], 1'b1};
            end
            {VSEW_32, VSEW_8 }: begin   // EEW / SEW = 4
                unique case (lmul_i)
                    LMUL_F8,
                    LMUL_F4: emul = EMUL_1;
                    LMUL_F2: emul = EMUL_2;
                    LMUL_1:  emul = EMUL_4;
                    LMUL_2:  emul = EMUL_8;
                    default: ;
                endcase
                vl   = {vl_i[CFG_VL_W-3:0], 2'b11};
            end
            default: ;
        endcase
    end

    logic pipeline_ready;
    always_comb begin
        op_ack_o       = 1'b0;
        misaligned_o   = 1'b0;
        state_valid_d  = state_valid_q;
        state_d        = state_q;

        if (((~state_valid_q) | (last_cycle & pipeline_ready)) & op_rdy_i) begin
            op_ack_o     = 1'b1;
            misaligned_o = (rs1_val_i[$clog2(VMEM_W/8)-1:0] != '0); // |
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
            state_d.mode        = mode_i;
            state_d.emul        = emul;
            state_d.vl          = vl;
            state_d.vl_0        = vl_0_i;
            state_d.base_addr   = rs1_val_i[31:0];
            state_d.rs2         = rs2_i;
            state_d.vs2_fetch   = rs2_i.vreg;
            state_d.vs2_shift   = 1'b1;
            state_d.vd          = vd_i;
            state_d.vs3_fetch   = mode_i.store;
            state_d.vs3_shift   = 1'b1;
            state_d.vd_store    = 1'b0;
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
                    LSU_UNITSTRIDE: state_d.base_addr = state_q.base_addr + (VMEM_W / 8);
                    LSU_STRIDED:    state_d.base_addr = state_q.base_addr + state_q.rs2.r.xval;
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
                state_d.vs2_shift = (state_q.count.part.stri == '1) | (state_q.mode.stride == LSU_UNITSTRIDE);
                state_d.vs3_shift = (state_q.count.part.stri == '1) | (state_q.mode.stride == LSU_UNITSTRIDE);
            end

            end
    end


    ///////////////////////////////////////////////////////////////////////////
    // LSU PIPELINE BUFFERS:

    // pass state information along pipeline:
    logic                       state_vreg_ready,   state_vs2_ready,   state_vs3_ready,   state_req_ready;
    logic     state_init_valid, state_vreg_valid_q, state_vs2_valid_q, state_vs3_valid_q, state_req_valid_q, state_rdata_valid_q, state_vd_valid_q;
    lsu_state state_init,       state_vreg_q,       state_vs2_q,       state_vs3_q,       state_req_q,       state_rdata_q,       state_vd_q;
    lsu_state state_rdata_d;
    always_comb begin
        state_init_valid      = state_valid_q;
        state_init            = state_q;
        state_init.last_cycle = state_valid_q & last_cycle;
        state_init.vd_store   = state_q.count.val[LSU_COUNTER_W-4:0] == '1;
    end
    assign pipeline_ready = state_vreg_ready;

    assign pending_load_o  = (state_init_valid   & ~state_init.mode.store  ) |
                             (state_vreg_valid_q & ~state_vreg_q.mode.store) |
                             (state_vs2_valid_q  & ~state_vs2_q.mode.store ) |
                             (state_vs3_valid_q  & ~state_vs3_q.mode.store ) |
                             (state_req_valid_q  & ~state_req_q.mode.store );
    assign pending_store_o = (state_init_valid   &  state_init.mode.store  ) |
                             (state_vreg_valid_q &  state_vreg_q.mode.store) |
                             (state_vs2_valid_q  &  state_vs2_q.mode.store ) |
                             (state_vs3_valid_q  &  state_vs3_q.mode.store ) |
                             (state_req_valid_q  &  state_req_q.mode.store );

    // common vreg read register:
    logic [VREG_W-1:0] vreg_rd_q, vreg_rd_d;

    // source vreg shift registers:
    logic [VREG_W-1:0] vs2_shift_q,   vs2_shift_d;
    logic [VREG_W-1:0] vs3_shift_q,   vs3_shift_d;
    logic [VREG_W-1:0] v0msk_shift_q, v0msk_shift_d;

    // temporary buffer for vs2 while fetching vs3:
    logic [31:0] vs2_tmp_q, vs2_tmp_d;

    // request address:
    logic [31:0] req_addr_q, req_addr_d;

    // store data and mask buffers:
    logic [VMEM_W  -1:0] wdata_buf_q, wdata_buf_d;
    logic [VMEM_W/8-1:0] wmask_buf_q, wmask_buf_d;

    // temporary buffer for byte mask during request:
    logic [VMEM_W/8-1:0] vmsk_tmp_q, vmsk_tmp_d;

    // load data, offset and mask buffers:
    logic [       VMEM_W   -1:0] rdata_buf_q, rdata_buf_d;
    logic [$clog2(VMEM_W/8)-1:0] rdata_off_q, rdata_off_d;
    logic [       VMEM_W/8 -1:0] rmask_buf_q, rmask_buf_d;

    // load data shift register:
    logic [VREG_W-1:0] vd_shift_q,    vd_shift_d;
    logic [VMSK_W-1:0] vdmsk_shift_q, vdmsk_shift_d;

    // vreg write buffers
    localparam WRITE_BUFFER_SZ = (MAX_WR_DELAY > 0) ? MAX_WR_DELAY : 1;
    logic              vreg_wr_en_q  [WRITE_BUFFER_SZ], vreg_wr_en_d;
    logic [4:0]        vreg_wr_addr_q[WRITE_BUFFER_SZ], vreg_wr_addr_d;
    logic [VMSK_W-1:0] vreg_wr_mask_q[WRITE_BUFFER_SZ], vreg_wr_mask_d;
    logic [VREG_W-1:0] vreg_wr_q     [WRITE_BUFFER_SZ], vreg_wr_d;

    // hazard clear registers
    logic [31:0] clear_rd_hazards_q, clear_rd_hazards_d;
    logic [31:0] clear_wr_hazards_q, clear_wr_hazards_d;

    generate
        if (BUF_VREG) begin
            always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_lsu_stage_vreg_valid
                if (~async_rst_ni) begin
                    state_vreg_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_vreg_valid_q <= 1'b0;
                end
                else if (state_vreg_ready) begin
                    state_vreg_valid_q <= state_init_valid;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_lsu_stage_vreg
                if (state_vreg_ready) begin
                    state_vreg_q <= state_init;
                    vreg_rd_q    <= vreg_rd_d;
                end
            end
            assign state_vreg_ready = ~state_vreg_valid_q | state_vs2_ready;
        end else begin
            always_comb begin
                state_vreg_valid_q = state_init_valid;
                state_vreg_q       = state_init;
                vreg_rd_q          = vreg_rd_d;
            end
            assign state_vreg_ready = state_vs2_ready;
        end

        always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_lsu_stage_vs2_valid
            if (~async_rst_ni) begin
                state_vs2_valid_q <= 1'b0;
            end
            else if (~sync_rst_ni) begin
                state_vs2_valid_q <= 1'b0;
            end
            else if (state_vs2_ready) begin
                state_vs2_valid_q <= state_vreg_valid_q;
            end
        end
        always_ff @(posedge clk_i) begin : vproc_lsu_stage_vs2
            if (state_vs2_ready) begin
                state_vs2_q <= state_vreg_q;
                vs2_shift_q <= vs2_shift_d;
            end
        end
        assign state_vs2_ready = ~state_vs2_valid_q | state_vs3_ready;

        always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_lsu_stage_vs3_valid
            if (~async_rst_ni) begin
                state_vs3_valid_q <= 1'b0;
            end
            else if (~sync_rst_ni) begin
                state_vs3_valid_q <= 1'b0;
            end
            else if (state_vs3_ready) begin
                state_vs3_valid_q <= state_vs2_valid_q;
            end
        end
        always_ff @(posedge clk_i) begin : vproc_lsu_stage_vs3
            if (state_vs3_ready) begin
                state_vs3_q   <= state_vs2_q;
                vs3_shift_q   <= vs3_shift_d;
                v0msk_shift_q <= v0msk_shift_d;
                vs2_tmp_q     <= vs2_tmp_d;
            end
        end
        assign state_vs3_ready = ~state_vs3_valid_q | state_req_ready;

        if (BUF_REQUEST) begin
             always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_lsu_stage_req_valid
                if (~async_rst_ni) begin
                    state_req_valid_q <= 1'b0;
                end
                else if (~sync_rst_ni) begin
                    state_req_valid_q <= 1'b0;
                end
                else if (state_req_ready) begin
                    state_req_valid_q <= state_vs3_valid_q;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_lsu_stage_req
                if (state_req_ready) begin
                    state_req_q <= state_vs3_q;
                    req_addr_q  <= req_addr_d;
                    wdata_buf_q <= wdata_buf_d;
                    wmask_buf_q <= wmask_buf_d;
                    vmsk_tmp_q  <= vmsk_tmp_d;
                end
            end
            assign state_req_ready = ~state_req_valid_q | (data_req_o & data_gnt_i);
        end else begin
            always_comb begin
                state_req_valid_q = state_vs3_valid_q;
                state_req_q       = state_vs3_q;
                req_addr_q        = req_addr_d;
                wdata_buf_q       = wdata_buf_d;
                wmask_buf_q       = wmask_buf_d;
                vmsk_tmp_q        = vmsk_tmp_d;
            end
            assign state_req_ready = data_req_o & data_gnt_i;
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
                    state_rdata_valid_q <= data_rvalid_i;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_lsu_stage_rdata
                if (data_rvalid_i) begin
                    state_rdata_q <= state_rdata_d;
                    rdata_buf_q   <= rdata_buf_d;
                    rdata_off_q   <= rdata_off_d;
                    rmask_buf_q   <= rmask_buf_d;
                end
            end
        end else begin
            always_comb begin
                state_rdata_valid_q = data_rvalid_i;
                state_rdata_q       = state_rdata_d;
                rdata_buf_q         = rdata_buf_d;
                rdata_off_q         = rdata_off_d;
                rmask_buf_q         = rmask_buf_d;
            end
        end

        always_ff @(posedge clk_i or negedge async_rst_ni) begin : vproc_lsu_stage_vd_valid
            if (~async_rst_ni) begin
                state_vd_valid_q <= 1'b0;
            end
            else if (~sync_rst_ni) begin
                state_vd_valid_q <= 1'b0;
            end
            else begin
                state_vd_valid_q <= state_rdata_valid_q;
            end
        end
        always_ff @(posedge clk_i) begin : vproc_lsu_stage_vd
            if (state_rdata_valid_q) begin
                state_vd_q    <= state_rdata_q;
                vd_shift_q    <= vd_shift_d;
                vdmsk_shift_q <= vdmsk_shift_d;
            end
        end

        if (MAX_WR_DELAY > 0) begin
            always_ff @(posedge clk_i) begin : vproc_lsu_wr_delay
                vreg_wr_en_q  [0] <= vreg_wr_en_d;
                vreg_wr_addr_q[0] <= vreg_wr_addr_d;
                vreg_wr_mask_q[0] <= vreg_wr_mask_d;
                vreg_wr_q     [0] <= vreg_wr_d;
                for (int i = 1; i < MAX_WR_DELAY; i++) begin
                    vreg_wr_en_q  [i] <= vreg_wr_en_q  [i-1];
                    vreg_wr_addr_q[i] <= vreg_wr_addr_q[i-1];
                    vreg_wr_mask_q[i] <= vreg_wr_mask_q[i-1];
                    vreg_wr_q     [i] <= vreg_wr_q     [i-1];
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
        clear_wr_hazards_d     = vreg_wr_en_d                 ? (32'b1 << vreg_wr_addr_d                ) : 32'b0;
        if (MAX_WR_DELAY > 0) begin
            clear_wr_hazards_d = vreg_wr_en_q[MAX_WR_DELAY-1] ? (32'b1 << vreg_wr_addr_q[MAX_WR_DELAY-1]) : 32'b0;
        end
    end
    assign clear_wr_hazards_o = clear_wr_hazards_q;

    // read hazard clearing
    assign clear_rd_hazards_d = state_init_valid ? (
        (state_init.vs2_fetch ? (32'b1 << state_init.rs2.r.vaddr) : 32'b0) |
        (state_init.vs3_fetch ? (32'b1 << state_init.vd         ) : 32'b0) |
        {31'b0, state_init.mode.masked & state_init.first_cycle}
    ) : 32'b0;
    assign clear_rd_hazards_o = clear_rd_hazards_q;


    ///////////////////////////////////////////////////////////////////////////
    // LSU READ/WRITE:

    // source register addressing and read:
    assign vreg_rd_addr_o = state_init.vs2_fetch ? state_init.rs2.r.vaddr : state_init.vd;
    assign vreg_rd_d      = vreg_rd_i;

    // operand shift registers assignment:
    fetch_info vs2_info, vs3_info;
    always_comb begin
        vs2_info.shift = state_vreg_q.vs2_shift;
        vs2_info.fetch = state_vreg_q.vs2_fetch;
        vs3_info.shift = state_vs2_q.vs3_shift;
        vs3_info.fetch = state_vs2_q.vs3_fetch;
    end
    //`VREGSHIFT_OPERAND_VSEW(VREG_W, 32, vs2_info, 1'b0, state_vreg_q.mode.eew, vreg_rd_q, vs2_shift_q, vs2_shift_d)
    `VREGSHIFT_OPERAND_VSEW(VREG_W, VMEM_W, vs3_info, 1'b0, state_vs2_q.mode.eew, vreg_rd_q, vs3_shift_q, vs3_shift_d)
    always_comb begin
        vs2_shift_d = vreg_rd_q;
        if (~state_vreg_q.vs2_fetch) begin
            //vs2_shift_d = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_vreg_q.mode.eew)
                VSEW_8:  vs2_shift_d[VREG_W-9 :0] = vs2_shift_q[VREG_W-1:8 ];
                VSEW_16: vs2_shift_d[VREG_W-17:0] = vs2_shift_q[VREG_W-1:16];
                VSEW_32: vs2_shift_d[VREG_W-33:0] = vs2_shift_q[VREG_W-1:32];
                default: ;
            endcase
        end
    end
    always_comb begin
        //vs3_shift_d   = vreg_rd_q;
        v0msk_shift_d = vreg_mask_i;
        //if (~state_vs2_q.vs3_fetch) begin
        //    if (state_vs2_q.mode.stride == LSU_UNITSTRIDE) begin
        //        vs3_shift_d[VREG_W-VMEM_W-1:0] = vs3_shift_q[VREG_W-1:VMEM_W];
        //    end else begin
        //        //vs3_shift_d = DONT_CARE_ZERO ? '0 : 'x;
        //        unique case (state_vs2_q.mode.eew)
        //            VSEW_8:  vs3_shift_d[VREG_W-9 :0] = vs3_shift_q[VREG_W-1:8 ];
        //            VSEW_16: vs3_shift_d[VREG_W-17:0] = vs3_shift_q[VREG_W-1:16];
        //            VSEW_32: vs3_shift_d[VREG_W-33:0] = vs3_shift_q[VREG_W-1:32];
        //        endcase
        //    end
        //end
        if (~state_vs2_q.first_cycle) begin
            if (state_vs2_q.mode.stride == LSU_UNITSTRIDE) begin
                v0msk_shift_d = DONT_CARE_ZERO ? '0 : 'x;
                unique case (state_vs2_q.mode.eew)
                    VSEW_8:  v0msk_shift_d[VREG_W-(VMEM_W/8 )-1:0] = v0msk_shift_q[VREG_W-1:VMEM_W/8 ];
                    VSEW_16: v0msk_shift_d[VREG_W-(VMEM_W/16)-1:0] = v0msk_shift_q[VREG_W-1:VMEM_W/16];
                    VSEW_32: v0msk_shift_d[VREG_W-(VMEM_W/32)-1:0] = v0msk_shift_q[VREG_W-1:VMEM_W/32];
                    default: ;
                endcase
            end else begin
                v0msk_shift_d[VREG_W-2:0] = v0msk_shift_q[VREG_W-1:1];
            end
        end
    end
    always_comb begin
        vs2_tmp_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_vs2_q.mode.eew)
            VSEW_8:  vs2_tmp_d = {24'b0, vs2_shift_q[7 :0]};
            VSEW_16: vs2_tmp_d = {16'b0, vs2_shift_q[15:0]};
            VSEW_32: vs2_tmp_d =         vs2_shift_q[31:0] ;
            default: ;
        endcase
    end

    // compose memory address:
    assign req_addr_d = (state_vs3_q.mode.stride == LSU_INDEXED) ? state_vs3_q.base_addr + vs2_tmp_q : state_vs3_q.base_addr;

    // convert element mask to byte mask
    logic [VMEM_W/8-1:0] byte_mask;
    always_comb begin
        byte_mask = DONT_CARE_ZERO ? '0 : 'x;
        unique case (state_vs3_q.mode.eew)
            VSEW_8: begin
                byte_mask = v0msk_shift_q[VMEM_W/8-1:0];
            end
            VSEW_16: begin
                for (int i = 0; i < VMEM_W / 16; i++) begin
                    byte_mask[i*2]   = v0msk_shift_q[i];
                    byte_mask[i*2+1] = v0msk_shift_q[i];
                end
            end
            VSEW_32: begin
                for (int i = 0; i < VMEM_W / 32; i++) begin
                    byte_mask[i*4]   = v0msk_shift_q[i];
                    byte_mask[i*4+1] = v0msk_shift_q[i];
                    byte_mask[i*4+2] = v0msk_shift_q[i];
                    byte_mask[i*4+3] = v0msk_shift_q[i];
                end
            end
            default: ;
        endcase
    end
    assign vmsk_tmp_d = byte_mask;

    // write data conversion and masking:
    logic [VREG_W-1:0] wdata_unit_vl_mask;
    logic              wdata_stri_mask;
    assign wdata_unit_vl_mask =   state_vs3_q.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_vs3_q.vl));
    assign wdata_stri_mask    = (~state_vs3_q.vl_0 & (state_vs3_q.count.val <= state_vs3_q.vl)) & (state_vs3_q.mode.masked ? v0msk_shift_q[0] : 1'b1);
    always_comb begin
        wdata_buf_d = DONT_CARE_ZERO ? '0 : 'x;
        wmask_buf_d = DONT_CARE_ZERO ? '0 : 'x;
        if (state_vs3_q.mode.stride == LSU_UNITSTRIDE) begin
            wdata_buf_d = vs3_shift_q[VMEM_W-1:0];
            wmask_buf_d = (state_vs3_q.mode.masked ? byte_mask : '1) & wdata_unit_vl_mask[state_vs3_q.count.val[LSU_COUNTER_W-1:LSU_STRI_COUNTER_EXT_W]*VMEM_W/8 +: VMEM_W/8];
        end else begin
            unique case (state_vs3_q.mode.eew)
                VSEW_8: begin
                    for (int i = 0; i < VMEM_W / 8 ; i++)
                        wdata_buf_d[i*8  +: 8 ] = vs3_shift_q[7 :0];
                    wmask_buf_d = {{VMEM_W/8-1{1'b0}},    wdata_stri_mask  } <<  req_addr_d[$clog2(VMEM_W/8)-1:0]                                    ;
                end
                VSEW_16: begin
                    for (int i = 0; i < VMEM_W / 16; i++)
                        wdata_buf_d[i*16 +: 16] = vs3_shift_q[15:0];
                    wmask_buf_d = {{VMEM_W/8-2{1'b0}}, {2{wdata_stri_mask}}} << (req_addr_d[$clog2(VMEM_W/8)-1:0] & ({$clog2(VMEM_W/8){1'b1}} << 1));
                end
                VSEW_32: begin
                    for (int i = 0; i < VMEM_W / 32; i++)
                        wdata_buf_d[i*32 +: 32] = vs3_shift_q[31:0];
                    wmask_buf_d = {{VMEM_W/8-4{1'b0}}, {4{wdata_stri_mask}}} << (req_addr_d[$clog2(VMEM_W/8)-1:0] & ({$clog2(VMEM_W/8){1'b1}} << 2));
                end
                default: ;
            endcase
        end
    end

    // queue for storing masks and offsets until the memory system fulfills the request:
    logic lsu_queue_ready;
    vproc_queue #(
        .WIDTH        ( $clog2(VMEM_W/8) + VMEM_W/8 + $bits(lsu_state)                ),
        .DEPTH        ( 4                                                             )
    ) lsu_queue (
        .clk_i        ( clk_i                                                         ),
        .async_rst_ni ( async_rst_ni                                                  ),
        .sync_rst_ni  ( sync_rst_ni                                                   ),
        .enq_ready_o  ( lsu_queue_ready                                               ),
        .enq_valid_i  ( state_req_valid_q & state_req_ready & ~state_req_q.mode.store ),
        .enq_data_i   ( {req_addr_q[$clog2(VMEM_W/8)-1:0], vmsk_tmp_q, state_req_q}   ),
        .deq_ready_i  ( data_rvalid_i                                                 ),
        .deq_valid_o  (                                                               ),
        .deq_data_o   ( {rdata_off_d, rmask_buf_d, state_rdata_d}                     )
    );

    // memory request:
    assign data_addr_o  = {req_addr_q[31:$clog2(VMEM_W/8)], {$clog2(VMEM_W/8){1'b0}}};
    assign data_req_o   = state_req_valid_q & lsu_queue_ready; // keep requesting next access while addressing is not complete
    assign data_we_o    = state_req_q.mode.store;
    assign data_be_o    = wmask_buf_q;
    assign data_wdata_o = wdata_buf_q;

    // load data:
    assign rdata_buf_d = data_rdata_i;

    // load data conversion:
    logic [VREG_W  -1:0] rdata_unit_vl_mask;
    logic [VMEM_W/8-1:0] rdata_unit_vdmsk;
    assign rdata_unit_vl_mask = state_rdata_q.vl_0 ? {VREG_W{1'b0}} : ({VREG_W{1'b1}} >> (~state_rdata_q.vl));
    assign rdata_unit_vdmsk   = (state_rdata_q.mode.masked ? rmask_buf_q : {VMEM_W/8{1'b1}}) & rdata_unit_vl_mask[state_rdata_q.count.val[LSU_COUNTER_W-1:LSU_STRI_COUNTER_EXT_W]*VMEM_W/8 +: VMEM_W/8];
    logic rdata_stri_vdmsk;
    assign rdata_stri_vdmsk = (~state_rdata_q.vl_0 & (state_rdata_q.count.val <= state_rdata_q.vl)) & (state_rdata_q.mode.masked ? rmask_buf_q[0] : 1'b1);
    always_comb begin
        vd_shift_d    = DONT_CARE_ZERO ? '0 : 'x;
        vdmsk_shift_d = DONT_CARE_ZERO ? '0 : 'x;
        if (state_rdata_q.mode.stride == LSU_UNITSTRIDE) begin
            vd_shift_d    = {rdata_buf_q     , vd_shift_q   [VREG_W-1:VMEM_W  ]};
            vdmsk_shift_d = {rdata_unit_vdmsk, vdmsk_shift_q[VMSK_W-1:VMEM_W/8]};
        end else begin
            unique case (state_rdata_q.mode.eew)
                VSEW_8: begin
                    vd_shift_d    = {rdata_buf_q[{3'b000, rdata_off_q                                  } * 8 +: 8 ], vd_shift_q   [VREG_W-1:8 ]};
                    vdmsk_shift_d = {   rdata_stri_vdmsk                                                           , vdmsk_shift_q[VMSK_W-1:1 ]};
                end
                VSEW_16: begin
                    vd_shift_d    = {rdata_buf_q[{3'b000, rdata_off_q & ({$clog2(VMEM_W/8){1'b1}} << 1)} * 8 +: 16], vd_shift_q   [VREG_W-1:16]};
                    vdmsk_shift_d = {{2{rdata_stri_vdmsk}}                                                         , vdmsk_shift_q[VMSK_W-1:2 ]};
                end
                VSEW_32: begin
                    vd_shift_d    = {rdata_buf_q[{3'b000, rdata_off_q & ({$clog2(VMEM_W/8){1'b1}} << 2)} * 8 +: 32], vd_shift_q   [VREG_W-1:32]};
                    vdmsk_shift_d = {{4{rdata_stri_vdmsk}}                                                         , vdmsk_shift_q[VMSK_W-1:4 ]};
                end
                default: ;
            endcase
        end
    end

    //
    assign vreg_wr_en_d   = state_vd_valid_q & state_vd_q.vd_store;
    assign vreg_wr_addr_d = state_vd_q.vd;
    assign vreg_wr_mask_d = vreg_wr_en_o ? vdmsk_shift_q : '0;
    assign vreg_wr_d      = vd_shift_q;

endmodule
