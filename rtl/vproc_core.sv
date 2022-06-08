// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_core import vproc_pkg::*; #(
        // XIF interface configuration (must be provided when instantiating this module)
        parameter int unsigned           XIF_ID_W                 = 0, // width of instruction IDs
        parameter int unsigned           XIF_MEM_W                = 0, // memory interface width

        // Vector register file configuration
        parameter vreg_type              VREG_TYPE                = vproc_config::VREG_TYPE,
        parameter int unsigned           VREG_W                   = vproc_config::VREG_W,
        parameter int unsigned           VPORT_RD_CNT             = vproc_config::VPORT_RD_CNT,
        parameter int unsigned           VPORT_RD_W[VPORT_RD_CNT] = vproc_config::VPORT_RD_W,
        parameter int unsigned           VPORT_WR_CNT             = vproc_config::VPORT_WR_CNT,
        parameter int unsigned           VPORT_WR_W[VPORT_WR_CNT] = vproc_config::VPORT_WR_W,

        // Vector pipeline configuration
        parameter int unsigned           PIPE_CNT                 = vproc_config::PIPE_CNT,
        parameter bit [UNIT_CNT-1:0]     PIPE_UNITS    [PIPE_CNT] = vproc_config::PIPE_UNITS,
        parameter int unsigned           PIPE_W        [PIPE_CNT] = vproc_config::PIPE_W,
        parameter int unsigned           PIPE_VPORT_CNT[PIPE_CNT] = vproc_config::PIPE_VPORT_CNT,
        parameter int unsigned           PIPE_VPORT_IDX[PIPE_CNT] = vproc_config::PIPE_VPORT_IDX,
        parameter int unsigned           PIPE_VPORT_WR [PIPE_CNT] = vproc_config::PIPE_VPORT_WR,

        // Unit-specific configuration
        parameter int unsigned           VLSU_QUEUE_SZ            = vproc_config::VLSU_QUEUE_SZ,
        parameter bit [VLSU_FLAGS_W-1:0] VLSU_FLAGS               = vproc_config::VLSU_FLAGS,
        parameter mul_type               MUL_TYPE                 = vproc_config::MUL_TYPE,

        // Miscellaneous configuration
        parameter int unsigned           INSTR_QUEUE_SZ           = vproc_config::INSTR_QUEUE_SZ,
        parameter bit [BUF_FLAGS_W-1:0]  BUF_FLAGS                = vproc_config::BUF_FLAGS,

        parameter bit                    DONT_CARE_ZERO           = 1'b0, // init don't cares to 0
        parameter bit                    ASYNC_RESET              = 1'b0  // rst_ni is async
    )(
        input  logic                     clk_i,
        input  logic                     rst_ni,

        // eXtension interface
        vproc_xif.coproc_issue           xif_issue_if,
        vproc_xif.coproc_commit          xif_commit_if,
        vproc_xif.coproc_mem             xif_mem_if,
        vproc_xif.coproc_mem_result      xif_memres_if,
        vproc_xif.coproc_result          xif_result_if,

        output logic                     pending_load_o,
        output logic                     pending_store_o,

        // CSR connections
        output logic [31:0]              csr_vtype_o,
        output logic [31:0]              csr_vl_o,
        output logic [31:0]              csr_vlenb_o,
        output logic [31:0]              csr_vstart_o,
        input  logic [31:0]              csr_vstart_i,
        input  logic                     csr_vstart_set_i,
        output logic [1:0]               csr_vxrm_o,
        input  logic [1:0]               csr_vxrm_i,
        input  logic                     csr_vxrm_set_i,
        output logic                     csr_vxsat_o,
        input  logic                     csr_vxsat_i,
        input  logic                     csr_vxsat_set_i,

        output logic [31:0]              pend_vreg_wr_map_o
    );

    if ((VREG_W & (VREG_W - 1)) != 0 || VREG_W < 64) begin
        $fatal(1, "The vector register width VREG_W must be at least 64 and a power of two.  ",
                  "The current value of %d is invalid.", VREG_W);
    end

    generate
        for (genvar i = 0; i < VPORT_RD_CNT; i++) begin
            if ((VPORT_RD_W[i] & (VPORT_RD_W[i] - 1)) != 0 || VPORT_RD_W[i] < 32) begin
                $fatal(1, "Vector register read port %d is %d bits wide, ", i, VPORT_RD_W[i],
                          "but a power of two between 32 and %d is required.", VREG_W);
            end
            if (VPORT_RD_W[i] > VREG_W) begin
                $fatal(1, "Vector register read port %d is %d bits wide, ", i, VPORT_RD_W[i],
                          "exceeds vector register width of %d bits.", VREG_W);
            end
        end
        for (genvar i = 0; i < VPORT_WR_CNT; i++) begin
            if ((VPORT_WR_W[i] & (VPORT_WR_W[i] - 1)) != 0 || VPORT_WR_W[i] < 32) begin
                $fatal(1, "Vector register write port %d is %d bits wide, ", i, VPORT_WR_W[i],
                          "but a power of two between 32 and %d is required.", VREG_W);
            end
            if (VPORT_WR_W[i] > VREG_W) begin
                $fatal(1, "Vector register write port %d is %d bits wide, ", i, VPORT_WR_W[i],
                          "exceeds vector register width of %d bits.", VREG_W);
            end
        end
    endgenerate

    generate
        for (genvar i = 0; i < PIPE_CNT; i++) begin
            if (PIPE_UNITS[i][UNIT_LSU] & (PIPE_W[i] != XIF_MEM_W)) begin
                $fatal(1, "The vector pipeline containing the VLSU must have a datapath width ",
                          "equal to the memory interface width.  However, pipeline %d ", i,
                          "containing the VLSU has a width of %d bits ", PIPE_W[i],
                          "while the memory interface is %d bits wide.", XIF_MEM_W);
            end
            if ((PIPE_VPORT_IDX[i] >= VPORT_RD_CNT) |
                (PIPE_VPORT_IDX[i] + PIPE_VPORT_CNT[i] > VPORT_RD_CNT)
            ) begin
                $fatal(1, "Vector pipeline %d uses vector register read port %d through %d, ", i,
                          PIPE_VPORT_IDX[i], PIPE_VPORT_IDX[i] + PIPE_VPORT_CNT[i] - 1,
                          "but the valid range is 0 through %d.", VPORT_RD_CNT - 1);
            end
            for (genvar j = i + 1; j < PIPE_CNT; j++) begin
                if (((PIPE_VPORT_IDX[i] < PIPE_VPORT_IDX[j]) &
                    (PIPE_VPORT_IDX[i] + PIPE_VPORT_CNT[i] > PIPE_VPORT_IDX[j])) |
                    ((PIPE_VPORT_IDX[i] >= PIPE_VPORT_IDX[j]) &
                    (PIPE_VPORT_IDX[j] + PIPE_VPORT_CNT[j] > PIPE_VPORT_IDX[i]))
                ) begin
                    $fatal(1, "Vector register read ports of vector pipeline %d overlap ", i,
                              "with the vector register read ports of vector pipeline %d ", j,
                              "(pipeline %d uses ports %d through %d ", i,
                              PIPE_VPORT_IDX[i], PIPE_VPORT_IDX[i] + PIPE_VPORT_CNT[i] - 1,
                              "and pipeline %d uses ports %d through %d).", j,
                              PIPE_VPORT_IDX[j], PIPE_VPORT_IDX[j] + PIPE_VPORT_CNT[j] - 1);
                end
            end
        end
    endgenerate

    typedef int unsigned ASSIGN_VADDR_RD_W_RET_T[VPORT_RD_CNT];
    typedef int unsigned ASSIGN_VADDR_WR_W_RET_T[VPORT_WR_CNT];
    function static ASSIGN_VADDR_RD_W_RET_T ASSIGN_VADDR_RD_W();
        for (int i = 0; i < VPORT_RD_CNT; i++) begin
            ASSIGN_VADDR_RD_W[i] = 5 + $clog2(VREG_W / VPORT_RD_W[i]);
        end
    endfunction
    function static ASSIGN_VADDR_WR_W_RET_T ASSIGN_VADDR_WR_W();
        for (int i = 0; i < VPORT_WR_CNT; i++) begin
            ASSIGN_VADDR_WR_W[i] = 5 + $clog2(VREG_W / VPORT_WR_W[i]);
        end
    endfunction

    localparam int unsigned VADDR_RD_W[VPORT_RD_CNT] = ASSIGN_VADDR_RD_W();
    localparam int unsigned VADDR_WR_W[VPORT_WR_CNT] = ASSIGN_VADDR_WR_W();

    function static int unsigned MAX_VPORT_RD_SLICE(
        int unsigned SRC[VPORT_RD_CNT], int unsigned OFFSET, int unsigned CNT
    );
        MAX_VPORT_RD_SLICE = 0;
        for (int i = 0; i < CNT; i++) begin
            if (SRC[i] > MAX_VPORT_RD_SLICE) begin
                MAX_VPORT_RD_SLICE = SRC[OFFSET + i];
            end
        end
    endfunction
    function static int unsigned MAX_VPORT_WR_SLICE(
        int unsigned SRC[VPORT_WR_CNT], int unsigned OFFSET, int unsigned CNT
    );
        MAX_VPORT_WR_SLICE = 0;
        for (int i = 0; i < CNT; i++) begin
            if (SRC[OFFSET + i] > MAX_VPORT_WR_SLICE) begin
                MAX_VPORT_WR_SLICE = SRC[OFFSET + i];
            end
        end
    endfunction

    localparam int unsigned MAX_VPORT_RD_W = MAX_VPORT_RD_SLICE(VPORT_RD_W, 0, VPORT_RD_CNT);
    localparam int unsigned MAX_VADDR_RD_W = MAX_VPORT_RD_SLICE(VADDR_RD_W, 0, VPORT_RD_CNT);
    localparam int unsigned MAX_VPORT_WR_W = MAX_VPORT_WR_SLICE(VPORT_WR_W, 0, VPORT_WR_CNT);
    localparam int unsigned MAX_VADDR_WR_W = MAX_VPORT_WR_SLICE(VADDR_WR_W, 0, VPORT_WR_CNT);
    localparam int unsigned MAX_VPORT_W    = (MAX_VPORT_RD_W > MAX_VPORT_WR_W) ? MAX_VPORT_RD_W : MAX_VPORT_WR_W;
    localparam int unsigned MAX_VADDR_W    = (MAX_VADDR_RD_W > MAX_VPORT_WR_W) ? MAX_VADDR_RD_W : MAX_VADDR_WR_W;

    // The current vector length (VL) actually counts bytes instead of elements.
    // Also, the vector lenght is actually one more element than what VL suggests;
    // hence, when VSEW = 8, the value in VL is the current length - 1,
    // when VSEW = 16 the actual vector length is VL / 2 + 1 and when VSEW = 32
    // the actual vector lenght is VL / 4 + 1. Due to this
    // encoding the top 3 bits of VL are only used when LMUL > 1.
    localparam int unsigned CFG_VL_W = $clog2(VREG_W); // width of the vl config register

    // Total count of instruction IDs used by the extension interface
    localparam int unsigned XIF_ID_CNT = 1 << XIF_ID_W;

    // define asynchronous and synchronous reset signals
    logic async_rst_n, sync_rst_n;
    assign async_rst_n = ASYNC_RESET ? rst_ni : 1'b1  ;
    assign sync_rst_n  = ASYNC_RESET ? 1'b1   : rst_ni;


    ///////////////////////////////////////////////////////////////////////////
    // CONFIGURATION STATE AND CSR READ AND WRITES

    cfg_vsew             vsew_q,     vsew_d;     // VSEW (single element width)
    cfg_lmul             lmul_q,     lmul_d;     // LMUL
    logic [1:0]          agnostic_q, agnostic_d; // agnostic policy (vta & vma)
    logic                vl_0_q,     vl_0_d;     // set if VL == 0
    logic [CFG_VL_W-1:0] vl_q,       vl_d;       // VL * (VSEW / 8) - 1
    logic [CFG_VL_W  :0] vl_csr_q,   vl_csr_d;   // VL (intentionally CFG_VL_W+1 wide)
    logic [CFG_VL_W-1:0] vstart_q,   vstart_d;   // vector start index
    cfg_vxrm             vxrm_q,     vxrm_d;     // fixed-point rounding mode
    logic                vxsat_q,    vxsat_d;    // fixed-point saturation flag
    always_ff @(posedge clk_i or negedge async_rst_n) begin : vproc_cfg_reg
        if (~async_rst_n) begin
            vsew_q     <= VSEW_INVALID;
            lmul_q     <= LMUL_1;
            agnostic_q <= '0;
            vl_0_q     <= 1'b0;
            vl_q       <= '0;
            vl_csr_q   <= '0;
            vstart_q   <= '0;
            vxrm_q     <= VXRM_RNU;
            vxsat_q    <= 1'b0;
        end
        else if (~sync_rst_n) begin
            vsew_q     <= VSEW_INVALID;
            lmul_q     <= LMUL_1;
            agnostic_q <= '0;
            vl_0_q     <= 1'b0;
            vl_q       <= '0;
            vl_csr_q   <= '0;
            vstart_q   <= '0;
            vxrm_q     <= VXRM_RNU;
            vxsat_q    <= 1'b0;
        end else begin
            vsew_q     <= vsew_d;
            lmul_q     <= lmul_d;
            agnostic_q <= agnostic_d;
            vl_0_q     <= vl_0_d;
            vl_q       <= vl_d;
            vl_csr_q   <= vl_csr_d;
            vstart_q   <= vstart_d;
            vxrm_q     <= vxrm_d;
            vxsat_q    <= vxsat_d;
        end
    end
    logic cfg_valid;
    assign cfg_valid = vsew_q != VSEW_INVALID;

    // CSR reads
    assign csr_vtype_o  = cfg_valid ? {24'b0, agnostic_q, 1'b0, vsew_q, lmul_q} : 32'h80000000;
    assign csr_vl_o     = cfg_valid ? {{(32-CFG_VL_W-1){1'b0}}, vl_csr_q} : '0;
    assign csr_vlenb_o  = VREG_W / 8;
    assign csr_vstart_o = '0;
    assign csr_vxrm_o   = vxrm_q;
    assign csr_vxsat_o  = vxsat_q;


    ///////////////////////////////////////////////////////////////////////////
    // VECTOR INSTRUCTION DECODER INTERFACE

    typedef struct packed {
        logic [XIF_ID_W-1:0] id;
        cfg_vsew             vsew;
        cfg_emul             emul;
        cfg_vxrm             vxrm;
        logic                vl_0;
        logic [CFG_VL_W-1:0] vl;
        op_unit              unit;
        op_mode              mode;
        op_widenarrow        widenarrow;
        op_regs              rs1;
        op_regs              rs2;
        op_regd              rd;
        logic                pend_load;
        logic                pend_store;
    } decoder_data;

    // signals for decoder and for decoder buffer
    logic        dec_ready,       dec_valid,       dec_clear;
    logic        dec_buf_valid_q, dec_buf_valid_d;
    decoder_data dec_data_q,      dec_data_d;
    always_ff @(posedge clk_i or negedge async_rst_n) begin : vproc_dec_buf_valid
        if (~async_rst_n) begin
            dec_buf_valid_q <= 1'b0;
        end
        else if (~sync_rst_n) begin
            dec_buf_valid_q <= 1'b0;
        end else begin
            dec_buf_valid_q <= dec_buf_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_dec_buf_data
        if (dec_ready) begin
            dec_data_q <= dec_data_d;
        end
    end
    assign dec_buf_valid_d = (~dec_ready | dec_valid) & ~dec_clear;

    // Stall instruction offloading in case the instruction ID is already used
    // by another instruction which is not complete
    logic instr_valid, issue_id_used;
    assign instr_valid = xif_issue_if.issue_valid & ~issue_id_used;

    op_unit instr_unit;
    op_mode instr_mode;
    vproc_decoder #(
        .DONT_CARE_ZERO ( DONT_CARE_ZERO               ),
        .CFG_VL_W       ( CFG_VL_W                     )
    ) dec (
        .instr_i        ( xif_issue_if.issue_req.instr ),
        .instr_valid_i  ( instr_valid                  ),
        .x_rs1_i        ( xif_issue_if.issue_req.rs[0] ),
        .x_rs2_i        ( xif_issue_if.issue_req.rs[1] ),
        .vsew_i         ( vsew_q                       ),
        .lmul_i         ( lmul_q                       ),
        .vxrm_i         ( vxrm_q                       ),
        .vl_i           ( vl_q                         ),
        .valid_o        ( dec_valid                    ),
        .vsew_o         ( dec_data_d.vsew              ),
        .emul_o         ( dec_data_d.emul              ),
        .vxrm_o         ( dec_data_d.vxrm              ),
        .vl_o           ( dec_data_d.vl                ),
        .unit_o         ( instr_unit                   ),
        .mode_o         ( instr_mode                   ),
        .widenarrow_o   ( dec_data_d.widenarrow        ),
        .rs1_o          ( dec_data_d.rs1               ),
        .rs2_o          ( dec_data_d.rs2               ),
        .rd_o           ( dec_data_d.rd                )
    );
    assign dec_data_d.id         = xif_issue_if.issue_req.id;
    assign dec_data_d.vl_0       = vl_0_q;
    assign dec_data_d.unit       = instr_unit;
    assign dec_data_d.mode       = instr_mode;
    assign dec_data_d.pend_load  = (instr_unit == UNIT_LSU) & ~instr_mode.lsu.store;
    assign dec_data_d.pend_store = (instr_unit == UNIT_LSU) &  instr_mode.lsu.store;

    // Note: The decoder is not ready if the decode buffer is not ready, even
    // if an offloaded instruction is illegal.  The decode buffer could hold a
    // vset[i]vl[i] instruction that will change the configuration in the next
    // cycle and any subsequent offloaded instruction must be validated w.r.t.
    // the new configuration.
    assign xif_issue_if.issue_ready          = dec_ready & ~issue_id_used;

    assign xif_issue_if.issue_resp.accept    = dec_valid;
    assign xif_issue_if.issue_resp.writeback = dec_valid & (((instr_unit == UNIT_ELEM) & instr_mode.elem.xreg) | (instr_unit == UNIT_CFG));
    assign xif_issue_if.issue_resp.dualwrite = 1'b0;
    assign xif_issue_if.issue_resp.dualread  = 1'b0;
    assign xif_issue_if.issue_resp.loadstore = dec_valid & (instr_unit == UNIT_LSU);
    assign xif_issue_if.issue_resp.exc       = dec_valid & (instr_unit == UNIT_LSU);


    ///////////////////////////////////////////////////////////////////////////
    // VECTOR INSTRUCTION COMMIT STATE

    // The instruction commit state masks track whether a vector instruction is
    // speculative or not and whether an instruction has been killed.  First,
    // any instruction ID is speculative (instr_notspec_q[id] == 1'b0), which
    // indicates that either no instruction with that ID has been offloaded yet
    // or if there is an instruction with that ID, then it is still speculative
    // (i.e., it has not been committed yet).  Once an instruction becomes non-
    // speculative (by being either committed or killed via the XIF commit
    // interface) the respective bit in instr_notspec_q is set; the bit remains
    // set until the instruction is complete.  Note that an instruction may be
    // incomplete despite having been retired (by providing a result to the
    // host CPU via the XIF result interface).  Hence, the host CPU might
    // attempt to reuse the ID of an incomplete instruction.  To avoid this,
    // the decoder stalls in case the instruction ID of a new instruction is
    // still marked as non-speculative (i.e., the corresponding bit in
    // instr_notspec_q is set).
    logic [XIF_ID_CNT-1:0] instr_notspec_q,   instr_notspec_d;   // not speculative mask
    logic [XIF_ID_CNT-1:0] instr_killed_q,    instr_killed_d;    // killed mask
    logic [XIF_ID_CNT-1:0] instr_empty_res_q, instr_empty_res_d; // empty result mask
    always_ff @(posedge clk_i or negedge async_rst_n) begin : vproc_commit_buf
        if (~async_rst_n) begin
            instr_notspec_q <= '0;
        end
        else if (~sync_rst_n) begin
            instr_notspec_q <= '0;
        end else begin
            instr_notspec_q <= instr_notspec_d;
        end
    end
    always_ff @(posedge clk_i) begin
        instr_killed_q    <= instr_killed_d;
        instr_empty_res_q <= instr_empty_res_d;
    end

    assign issue_id_used = instr_notspec_q[xif_issue_if.issue_req.id];

    // Instruction complete signal for each pipeline
    logic [PIPE_CNT-1:0]               instr_complete_valid;
    logic [PIPE_CNT-1:0][XIF_ID_W-1:0] instr_complete_id;

    // return an empty result or VL as result
    logic                result_empty_valid, result_csr_valid;
    logic                                    result_csr_ready;
    logic [XIF_ID_W-1:0] result_empty_id,    result_csr_id;
    logic [4:0]                              result_csr_addr;
    logic                                    result_csr_delayed;
    logic [31:0]                             result_csr_data;

    logic queue_ready, queue_push; // instruction queue ready and push signals (enqueue handshake)
    assign queue_push = dec_buf_valid_q & (dec_data_q.unit != UNIT_CFG);

    // decode buffer is vacated either by enqueueing an instruction or for
    // vset[i]vl[i] once the instruction has been committed; for vset[i]vl[i]
    // it will take an additional cycle until the CSR values are updated, hence
    // the decode buffer is cleared without asserting dec_ready
    assign dec_ready = ~dec_buf_valid_q | (queue_ready & queue_push);

    always_comb begin
        instr_notspec_d    = instr_notspec_q;
        instr_killed_d     = instr_killed_q;
        instr_empty_res_d  = instr_empty_res_q;
        result_csr_valid   = 1'b0;
        result_csr_id      = dec_data_q.id;
        result_csr_addr    = dec_data_q.rd.addr;
        result_empty_valid = 1'b0;
        result_empty_id    = xif_commit_if.commit.id;
        dec_clear          = 1'b0;

        if (xif_issue_if.issue_valid) begin
            // For each issued instruction, remember whether it will produce an
            // empty result or not. This must be done for accepted as well as
            // rejected instructions, since the main core will commit all of
            // them and rejected instructions must not produce a result.
            instr_empty_res_d[xif_issue_if.issue_req.id] = xif_issue_if.issue_resp.accept & ~xif_issue_if.issue_resp.writeback & ~xif_issue_if.issue_resp.loadstore;
        end
        if (xif_commit_if.commit_valid) begin
            // Generate an empty result for all instructions except those that
            // writeback to the main core and for vector loads and stores
            if (~xif_commit_if.commit.commit_kill) begin
                if (dec_valid & (xif_issue_if.issue_req.id == xif_commit_if.commit.id)) begin
                    result_empty_valid = ~xif_issue_if.issue_resp.writeback & ~xif_issue_if.issue_resp.loadstore;
                end else begin
                    result_empty_valid = instr_empty_res_q[xif_commit_if.commit.id];
                end
            end

            if (dec_buf_valid_q & (dec_data_q.unit == UNIT_CFG) & (dec_data_q.id == xif_commit_if.commit.id)) begin
                // Configuration instructions are not enqueued.  The instruction
                // is retired and the result returned as soon as it is
                // committed.
                result_csr_valid = ~xif_commit_if.commit.commit_kill;
                if (result_csr_ready | xif_commit_if.commit.commit_kill) begin
                    dec_clear = 1'b1;
                end else begin
                    instr_notspec_d[xif_commit_if.commit.id] = 1'b1;
                end
            end else begin
                instr_notspec_d[xif_commit_if.commit.id] = 1'b1;
            end

            instr_killed_d[xif_commit_if.commit.id] = xif_commit_if.commit.commit_kill;
        end
        if (dec_buf_valid_q & (dec_data_q.unit == UNIT_CFG) & instr_notspec_q[dec_data_q.id]) begin
            // Execute a configuration instruction that has already been
            // committed earlier (i.e., while decoding and accepting the
            // instruction).
            result_csr_valid = ~instr_killed_q[dec_data_q.id];
            if (result_csr_ready | instr_killed_q[dec_data_q.id]) begin
                dec_clear                      = 1'b1;
                instr_notspec_d[dec_data_q.id] = 1'b0;
            end
        end
        for (int i = 0; i < PIPE_CNT; i++) begin
            if (instr_complete_valid[i]) begin
                instr_notspec_d[instr_complete_id[i]] = 1'b0;
            end
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // VSET[I]VL[I] CONFIGURATION UPDATE LOGIC

    // temporary variables for calculating new vector length for vset[i]vl[i]
    logic [33:0] cfg_avl;   // AVL * (VSEW / 8) - 1
    always_comb begin
        cfg_avl = DONT_CARE_ZERO ? '0 : 'x;
        unique case (dec_data_q.mode.cfg.vsew)
            VSEW_8:  cfg_avl = {2'b00, dec_data_q.rs1.r.xval - 1       };
            VSEW_16: cfg_avl = {1'b0 , dec_data_q.rs1.r.xval - 1, 1'b1 };
            VSEW_32: cfg_avl = {       dec_data_q.rs1.r.xval - 1, 2'b11};
            default: ;
        endcase
    end

    // CSR read/write logic
    logic [1:0] vxrm_next;
    assign vxrm_d = cfg_vxrm'(vxrm_next);
    always_comb begin
        vsew_d     = vsew_q;
        lmul_d     = lmul_q;
        agnostic_d = agnostic_q;
        vl_0_d     = vl_0_q;
        vl_d       = vl_q;
        vl_csr_d   = vl_csr_q;
        vstart_d   = vstart_q;
        vxrm_next  = vxrm_q;
        vxsat_d    = vxsat_q;

        result_csr_delayed = DONT_CARE_ZERO ? '0 : 'x;
        result_csr_data    = DONT_CARE_ZERO ? '0 : 'x;

        // regular CSR register read/write
        if (result_csr_valid) begin
            result_csr_delayed = 1'b0; // result is the current (old) value for regular CSR reads
            unique case (dec_data_q.mode.cfg.csr_op)
                CFG_VTYPE_READ:   result_csr_data = csr_vtype_o;
                CFG_VL_READ:      result_csr_data = csr_vl_o;
                CFG_VLENB_READ:   result_csr_data = csr_vlenb_o;
                CFG_VSTART_WRITE,
                CFG_VSTART_SET,
                CFG_VSTART_CLEAR: result_csr_data = {{(32-CFG_VL_W){1'b0}}, vstart_q};
                CFG_VXSAT_WRITE,
                CFG_VXSAT_SET,
                CFG_VXSAT_CLEAR:  result_csr_data = {31'b0, vxsat_q};
                CFG_VXRM_WRITE,
                CFG_VXRM_SET,
                CFG_VXRM_CLEAR:   result_csr_data = {30'b0, vxrm_q};
                CFG_VCSR_WRITE,
                CFG_VCSR_SET,
                CFG_VCSR_CLEAR:   result_csr_data = {29'b0, vxrm_q, vxsat_q};
                default: ;
            endcase
            // update read/write CSR
            unique case (dec_data_q.mode.cfg.csr_op)
                CFG_VSTART_WRITE: vstart_d              =  dec_data_q.rs1.r.xval[CFG_VL_W-1:0];
                CFG_VSTART_SET:   vstart_d             |=  dec_data_q.rs1.r.xval[CFG_VL_W-1:0];
                CFG_VSTART_CLEAR: vstart_d             &= ~dec_data_q.rs1.r.xval[CFG_VL_W-1:0];
                CFG_VXSAT_WRITE:  vxsat_d               =  dec_data_q.rs1.r.xval[0         :0];
                CFG_VXSAT_SET:    vxsat_d              |=  dec_data_q.rs1.r.xval[0         :0];
                CFG_VXSAT_CLEAR:  vxsat_d              &= ~dec_data_q.rs1.r.xval[0         :0];
                CFG_VXRM_WRITE:   vxrm_next             =  dec_data_q.rs1.r.xval[1         :0];
                CFG_VXRM_SET:     vxrm_next            |=  dec_data_q.rs1.r.xval[1         :0];
                CFG_VXRM_CLEAR:   vxrm_next            &= ~dec_data_q.rs1.r.xval[1         :0];
                CFG_VCSR_WRITE:   {vxrm_next, vxsat_d}  =  dec_data_q.rs1.r.xval[2         :0];
                CFG_VCSR_SET:     {vxrm_next, vxsat_d} |=  dec_data_q.rs1.r.xval[2         :0];
                CFG_VCSR_CLEAR:   {vxrm_next, vxsat_d} &= ~dec_data_q.rs1.r.xval[2         :0];
                default: ;
            endcase
        end

        // update configuration state for vset[i]vl[i] instructions
        if (result_csr_valid & (dec_data_q.mode.cfg.csr_op == CFG_VSETVL)) begin
            vsew_d             = dec_data_q.mode.cfg.vsew;
            lmul_d             = dec_data_q.mode.cfg.lmul;
            agnostic_d         = dec_data_q.mode.cfg.agnostic;
            result_csr_delayed = 1'b1; // result is the updated value, hence delayed by one cycle
            if (dec_data_q.mode.cfg.keep_vl) begin
                // Change VSEW and LMUL while keeping the current VL. Note that the spec states:
                // > This form can only be used when VLMAX and hence vl is not actually changed by
                // > the new SEW/LMUL ratio. Use of the instruction with a new SEW/LMUL ratio that
                // > would result in a change of VLMAX is reserved. Implementations may set vill in
                // > this case.
                // Despite keeping the same VL, the `vl_q` register is a byte count and needs to be
                // updated. Changes to the current SEW/LMUL ratio result set VSEW to VSEW_INVALID.
                vl_d = DONT_CARE_ZERO ? '0 : 'x;
                unique case ({vsew_q, dec_data_q.mode.cfg.vsew})
                    // VSEW scaled by 4
                    {VSEW_8 , VSEW_32}: begin
                        vl_d = {vl_q[CFG_VL_W-3:0], 2'b11}; // vl_d = (vl_q + 1) * 4 - 1
                        unique case ({lmul_q, dec_data_q.mode.cfg.lmul})
                            {LMUL_F8, LMUL_F2},
                            {LMUL_F4, LMUL_1 },
                            {LMUL_F2, LMUL_2 },
                            {LMUL_1 , LMUL_4 },
                            {LMUL_2 , LMUL_8 }: ;
                            default: vsew_d = VSEW_INVALID;
                        endcase
                    end
                    // VSEW scaled by 2
                    {VSEW_8 , VSEW_16},
                    {VSEW_16, VSEW_32}: begin
                        vl_d = {vl_q[CFG_VL_W-2:0], 1'b1}; // vl_d = (vl_q + 1) * 2 - 1
                        unique case ({lmul_q, dec_data_q.mode.cfg.lmul})
                            {LMUL_F8, LMUL_F4},
                            {LMUL_F4, LMUL_F2},
                            {LMUL_F2, LMUL_1 },
                            {LMUL_1 , LMUL_2 },
                            {LMUL_2 , LMUL_4 },
                            {LMUL_4 , LMUL_8 }: ;
                            default: vsew_d = VSEW_INVALID;
                        endcase
                    end
                    // VSEW scaled by 1
                    {VSEW_8 , VSEW_8 },
                    {VSEW_16, VSEW_16},
                    {VSEW_32, VSEW_32}: begin
                        vl_d = vl_q;
                        if (lmul_q != dec_data_q.mode.cfg.lmul) begin
                            vsew_d = VSEW_INVALID;
                        end
                    end
                    // VSEW scaled by 1/2
                    {VSEW_16, VSEW_8 },
                    {VSEW_32, VSEW_16}: begin
                        vl_d = {1'b0, vl_q[CFG_VL_W-1:1]}; // vl_d = vl_q / 2
                        unique case ({lmul_q, dec_data_q.mode.cfg.lmul})
                            {LMUL_F4, LMUL_F8},
                            {LMUL_F2, LMUL_F4},
                            {LMUL_1 , LMUL_F2},
                            {LMUL_2 , LMUL_1 },
                            {LMUL_4 , LMUL_2 },
                            {LMUL_8 , LMUL_4 }: ;
                            default: vsew_d = VSEW_INVALID;
                        endcase
                    end
                    // VSEW scaled by 1/4
                    {VSEW_32, VSEW_8 }: begin
                        vl_d = {2'b00, vl_q[CFG_VL_W-1:2]}; // vl_d = vl_q / 4
                        unique case ({lmul_q, dec_data_q.mode.cfg.lmul})
                            {LMUL_F2, LMUL_F8},
                            {LMUL_1 , LMUL_F4},
                            {LMUL_2 , LMUL_F2},
                            {LMUL_4 , LMUL_1 },
                            {LMUL_8 , LMUL_2 }: ;
                            default: vsew_d = VSEW_INVALID;
                        endcase
                    end
                    default: ;
                endcase
            end else begin
                // Vicuna supports all integer LMUL settings combined with any legal SEW setting.
                // Fractional LMUL support covers the minimum requirements of the V specification:
                // > Implementations must provide fractional LMUL settings [...] to support
                // > LMUL ≥ SEWMIN/ELEN, where SEWMIN is the narrowest supported SEW value and ELEN
                // > is the widest supported SEW value.
                // The minimum SEW is 8 and ELEN is 32, hence Vicuna supports LMULs of 1/2 and 1/4.
                // However, the fractional LMUL cannot be combined with any SEW. The spec states:
                // > For a given supported fractional LMUL setting, implementations must support
                // > SEW settings between SEWMIN and LMUL * ELEN, inclusive.
                // LMUL 1/4 is only compatible with a SEW of 8 and LMUL 1/2 with a SEW of 8 and 16.
                // Attempts to use an illegal combination sets the `vill` bit in `vtype` (by
                // overwriting the VSEW setting with VSEW_INVALID.
                vl_0_d = 1'b0;
                vl_d   = DONT_CARE_ZERO ? '0 : 'x;
                unique case (dec_data_q.mode.cfg.lmul)
                    LMUL_F4: vl_d = ((cfg_avl[33:CFG_VL_W-5] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] : {5'b00000, {(CFG_VL_W-5){1'b1}}};
                    LMUL_F2: vl_d = ((cfg_avl[33:CFG_VL_W-4] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] : {4'b0000,  {(CFG_VL_W-4){1'b1}}};
                    LMUL_1 : vl_d = ((cfg_avl[33:CFG_VL_W-3] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] : {3'b000,   {(CFG_VL_W-3){1'b1}}};
                    LMUL_2 : vl_d = ((cfg_avl[33:CFG_VL_W-2] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] : {2'b00,    {(CFG_VL_W-2){1'b1}}};
                    LMUL_4 : vl_d = ((cfg_avl[33:CFG_VL_W-1] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] : {1'b0,     {(CFG_VL_W-1){1'b1}}};
                    LMUL_8 : vl_d = ((cfg_avl[33:CFG_VL_W  ] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] :            { CFG_VL_W   {1'b1}} ;
                    default: ;
                endcase
                vl_csr_d = DONT_CARE_ZERO ? '0 : 'x;
                unique case ({dec_data_q.mode.cfg.lmul, dec_data_q.mode.cfg.vsew})
                    {LMUL_F4, VSEW_8 },
                    {LMUL_F2, VSEW_16},
                    {LMUL_1 , VSEW_32}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-5] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {6'b1, {(CFG_VL_W-5){1'b0}}};
                    {LMUL_F2, VSEW_8 },
                    {LMUL_1 , VSEW_16},
                    {LMUL_2 , VSEW_32}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-4] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {5'b1, {(CFG_VL_W-4){1'b0}}};
                    {LMUL_1 , VSEW_8 },
                    {LMUL_2 , VSEW_16},
                    {LMUL_4 , VSEW_32}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-3] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {4'b1, {(CFG_VL_W-3){1'b0}}};
                    {LMUL_2 , VSEW_8 },
                    {LMUL_4 , VSEW_16},
                    {LMUL_8 , VSEW_32}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-2] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {3'b1, {(CFG_VL_W-2){1'b0}}};
                    {LMUL_4 , VSEW_8 },
                    {LMUL_8 , VSEW_16}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-1] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {2'b1, {(CFG_VL_W-1){1'b0}}};
                    {LMUL_8 , VSEW_8 }: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W  ] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {1'b1, {(CFG_VL_W  ){1'b0}}};
                    default: vsew_d = VSEW_INVALID;
                endcase
            end
            if ((dec_data_q.rs1.r.xval == 32'b0) & ~dec_data_q.mode.cfg.vlmax & ~dec_data_q.mode.cfg.keep_vl) begin
                vl_0_d   = 1'b1;
                vl_d     = {CFG_VL_W{1'b0}};
                vl_csr_d = '0;
            end
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // INSTRUCTION QUEUE

    // acknowledge signal from the dispatcher (indicate that an instruction has
    // been accepted for execution on an execution unit)
    logic op_ack;

    // instruction queue output signals
    logic        queue_valid_q,      queue_valid_d;
    decoder_data queue_data_q,       queue_data_d;
    logic [31:0] queue_pending_wr_q, queue_pending_wr_d; // potential write hazards
    generate
        // add an extra pipeline stage to calculate the hazards
        if (BUF_FLAGS[BUF_DEQUEUE]) begin
            always_ff @(posedge clk_i or negedge async_rst_n) begin : vproc_queue_valid
                if (~async_rst_n) begin
                    queue_valid_q <= 1'b0;
                end
                else if (~sync_rst_n) begin
                    queue_valid_q <= 1'b0;
                end
                else if ((~queue_valid_q) | op_ack) begin
                    queue_valid_q <= queue_valid_d;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_queue_data
                // move in next instruction when this buffer stage is empty
                // or when the current instruction is acknowledged
                if ((~queue_valid_q) | op_ack) begin
                    queue_data_q       <= queue_data_d;
                    queue_pending_wr_q <= queue_pending_wr_d;
                end
            end
        end else begin
            assign queue_valid_q      = queue_valid_d;
            assign queue_data_q       = queue_data_d;
            assign queue_pending_wr_q = queue_pending_wr_d;
        end
    endgenerate

    // instruction queue
    decoder_data queue_flags_any;
    generate
        if (INSTR_QUEUE_SZ > 0) begin
            vproc_queue #(
                .WIDTH        ( $bits(decoder_data)     ),
                .DEPTH        ( INSTR_QUEUE_SZ          )
            ) instr_queue (
                .clk_i        ( clk_i                   ),
                .async_rst_ni ( async_rst_n             ),
                .sync_rst_ni  ( sync_rst_n              ),
                .enq_ready_o  ( queue_ready             ),
                .enq_valid_i  ( queue_push              ),
                .enq_data_i   ( dec_data_q              ),
                .deq_ready_i  ( ~queue_valid_q | op_ack ),
                .deq_valid_o  ( queue_valid_d           ),
                .deq_data_o   ( queue_data_d            ),
                .flags_any_o  ( queue_flags_any         ),
                .flags_all_o  (                         )
            );
        end else begin
            assign queue_valid_d = queue_push;
            assign queue_ready   = ~queue_valid_q | op_ack;
            assign queue_data_d  = dec_data_q;
        end
    endgenerate

    // potential vector register hazards of the currently dequeued instruction
    vproc_pending_wr #(
        .DONT_CARE_ZERO ( DONT_CARE_ZERO          )
    ) queue_pending_wr (
        .vsew_i         ( queue_data_d.vsew       ),
        .emul_i         ( queue_data_d.emul       ),
        .unit_i         ( queue_data_d.unit       ),
        .mode_i         ( queue_data_d.mode       ),
        .widenarrow_i   ( queue_data_d.widenarrow ),
        .rd_i           ( queue_data_d.rd         ),
        .pending_wr_o   ( queue_pending_wr_d      )
    );

    // keep track of pending loads and stores
    logic pending_load_lsu, pending_store_lsu;
    assign pending_load_o  = (dec_buf_valid_q & dec_data_q.pend_load      ) |
                                                queue_flags_any.pend_load   |
                             (queue_valid_q   & queue_data_q.pend_load    ) |
                             pending_load_lsu;
    assign pending_store_o = (dec_buf_valid_q & dec_data_q.pend_store     ) |
                                                queue_flags_any.pend_store  |
                             (queue_valid_q   & queue_data_q.pend_store   ) |
                             pending_store_lsu;


    ///////////////////////////////////////////////////////////////////////////
    // DISPATCHER

    logic [PIPE_CNT-1:0]       pipe_instr_valid;
    logic [PIPE_CNT-1:0]       pipe_instr_ready;
    decoder_data               pipe_instr_data;
    logic [PIPE_CNT-1:0][31:0] pipe_clear_pend_vreg_wr;
    logic               [31:0] pend_vreg_wr_map;
    vproc_dispatcher #(
        .PIPE_CNT             ( PIPE_CNT                ),
        .PIPE_UNITS           ( PIPE_UNITS              ),
        .MAX_VADDR_W          ( 5                       ),
        .DECODER_DATA_T       ( decoder_data            ),
        .DONT_CARE_ZERO       ( DONT_CARE_ZERO          )
    ) dispatcher (
        .clk_i                ( clk_i                   ),
        .async_rst_ni         ( async_rst_n             ),
        .sync_rst_ni          ( sync_rst_n              ),
        .instr_valid_i        ( queue_valid_q           ),
        .instr_ready_o        ( op_ack                  ),
        .instr_data_i         ( queue_data_q            ),
        .instr_vreg_wr_i      ( queue_pending_wr_q      ),
        .dispatch_valid_o     ( pipe_instr_valid        ),
        .dispatch_ready_i     ( pipe_instr_ready        ),
        .dispatch_data_o      ( pipe_instr_data         ),
        .pend_vreg_wr_map_o   ( pend_vreg_wr_map        ),
        .pend_vreg_wr_clear_i ( pipe_clear_pend_vreg_wr )
    );
    assign pend_vreg_wr_map_o = pend_vreg_wr_map;


    ///////////////////////////////////////////////////////////////////////////
    // REGISTER FILE AND EXECUTION UNITS

    // register file:
    logic [VPORT_WR_CNT-1:0]               vregfile_wr_en_q,   vregfile_wr_en_d;
    logic [VPORT_WR_CNT-1:0][4:0]          vregfile_wr_addr_q, vregfile_wr_addr_d;
    logic [VPORT_WR_CNT-1:0][VREG_W  -1:0] vregfile_wr_data_q, vregfile_wr_data_d;
    logic [VPORT_WR_CNT-1:0][VREG_W/8-1:0] vregfile_wr_mask_q, vregfile_wr_mask_d;
    logic [VPORT_RD_CNT-1:0][4:0]          vregfile_rd_addr;
    logic [VPORT_RD_CNT-1:0][VREG_W  -1:0] vregfile_rd_data;
    vproc_vregfile #(
        .VREG_W       ( VREG_W             ),
        .MAX_PORT_W   ( MAX_VPORT_W        ),
        .MAX_ADDR_W   ( MAX_VADDR_W        ),
        .PORT_RD_CNT  ( VPORT_RD_CNT       ),
        .PORT_RD_W    ( VPORT_RD_W         ),
        .PORT_WR_CNT  ( VPORT_WR_CNT       ),
        .PORT_WR_W    ( VPORT_WR_W         ),
        .VREG_TYPE    ( VREG_TYPE          )
    ) vregfile (
        .clk_i        ( clk_i              ),
        .async_rst_ni ( async_rst_n        ),
        .sync_rst_ni  ( sync_rst_n         ),
        .wr_addr_i    ( vregfile_wr_addr_q ),
        .wr_data_i    ( vregfile_wr_data_q ),
        .wr_be_i      ( vregfile_wr_mask_q ),
        .wr_we_i      ( vregfile_wr_en_q   ),
        .rd_addr_i    ( vregfile_rd_addr   ),
        .rd_data_o    ( vregfile_rd_data   )
    );

    logic [VREG_W-1:0] vreg_mask;
    assign vreg_mask           = vregfile_rd_data[0];
    assign vregfile_rd_addr[0] = 5'b0;

    generate
        if (BUF_FLAGS[BUF_VREG_WR]) begin
            always_ff @(posedge clk_i) begin
                for (int i = 0; i < VPORT_WR_CNT; i++) begin
                    vregfile_wr_en_q  [i] <= vregfile_wr_en_d  [i];
                    vregfile_wr_addr_q[i] <= vregfile_wr_addr_d[i];
                    vregfile_wr_data_q[i] <= vregfile_wr_data_d[i];
                    vregfile_wr_mask_q[i] <= vregfile_wr_mask_d[i];
                end
            end
        end else begin
            always_comb begin
                for (int i = 0; i < VPORT_WR_CNT; i++) begin
                    vregfile_wr_en_q  [i] = vregfile_wr_en_d  [i];
                    vregfile_wr_addr_q[i] = vregfile_wr_addr_d[i];
                    vregfile_wr_data_q[i] = vregfile_wr_data_d[i];
                    vregfile_wr_mask_q[i] = vregfile_wr_mask_d[i];
                end
            end
        end
    endgenerate


    // Pending reads
    logic [PIPE_CNT-1:0][31:0] pipe_vreg_pend_rd_by_q, pipe_vreg_pend_rd_by_d;
    logic [PIPE_CNT-1:0][31:0] pipe_vreg_pend_rd_to_q, pipe_vreg_pend_rd_to_d;
    generate
        if (BUF_FLAGS[BUF_VREG_PEND]) begin
            // Note: A vreg write cannot happen within the first two cycles of
            // an instruction, hence delaying the pending vreg reads signals by
            // two cycles should cause no issues. This adds two unnecessary
            // extra stall cycles in case a write is blocked by a pending read
            // but that should happen rarely anyways.
            always_ff @(posedge clk_i) begin
                pipe_vreg_pend_rd_by_q <= pipe_vreg_pend_rd_by_d;
                pipe_vreg_pend_rd_to_q <= pipe_vreg_pend_rd_to_d;
            end
        end else begin
            assign pipe_vreg_pend_rd_by_q = pipe_vreg_pend_rd_by_d;
            assign pipe_vreg_pend_rd_to_q = pipe_vreg_pend_rd_to_d;
        end
    endgenerate
    logic [PIPE_CNT-1:0][31:0] pipe_vreg_pend_rd_in, pipe_vreg_pend_rd_out;
    always_comb begin
        pipe_vreg_pend_rd_in   = pipe_vreg_pend_rd_to_q;
        pipe_vreg_pend_rd_by_d = pipe_vreg_pend_rd_out;
        pipe_vreg_pend_rd_to_d = '0;
        for (int i = 0; i < PIPE_CNT; i++) begin
            for (int j = 0; j < PIPE_CNT; j++) begin
                if (i != j) begin
                    pipe_vreg_pend_rd_to_d[i] |= pipe_vreg_pend_rd_by_q[j];
                end
            end
        end
    end

    logic [PIPE_CNT-1:0]               pipe_vreg_wr_valid;
    logic [PIPE_CNT-1:0]               pipe_vreg_wr_ready;
    logic [PIPE_CNT-1:0][4:0]          pipe_vreg_wr_addr;
    logic [PIPE_CNT-1:0][VREG_W  -1:0] pipe_vreg_wr_data;
    logic [PIPE_CNT-1:0][VREG_W/8-1:0] pipe_vreg_wr_be;
    logic [PIPE_CNT-1:0]               pipe_vreg_wr_clr;
    logic [PIPE_CNT-1:0][1:0]          pipe_vreg_wr_clr_cnt;

    logic                lsu_trans_complete_valid;
    logic                lsu_trans_complete_ready;
    logic [XIF_ID_W-1:0] lsu_trans_complete_id;
    logic                lsu_trans_complete_exc;
    logic [5:0]          lsu_trans_complete_exccode;

    logic                elem_xreg_valid;
    logic                elem_xreg_ready;
    logic [XIF_ID_W-1:0] elem_xreg_id;
    logic [4:0]          elem_xreg_addr;
    logic [31:0]         elem_xreg_data;

    // TODO move below function together with the entire repeated writes logic into the vreg write mux module
    function static int unsigned MAX_WR_ATTEMPTS(int unsigned PIPE_IDX);
        MAX_WR_ATTEMPTS = 1;
        for (int i = 0; i < PIPE_IDX; i++) begin
            if (PIPE_VPORT_WR[i] == PIPE_VPORT_WR[PIPE_IDX]) begin
                MAX_WR_ATTEMPTS += 1;
            end
        end
    endfunction

    generate
        for (genvar i = 0; i < PIPE_CNT; i++) begin
`ifndef VERILATOR
            // Currently not possible in Verilator due to https://github.com/verilator/verilator/issues/3433
            localparam int unsigned PIPE_VPORT_W[PIPE_VPORT_CNT[i]]  = VPORT_RD_W[PIPE_VPORT_IDX[i] +: PIPE_VPORT_CNT[i]];
            localparam int unsigned PIPE_VADDR_W[PIPE_VPORT_CNT[i]]  = VADDR_RD_W[PIPE_VPORT_IDX[i] +: PIPE_VPORT_CNT[i]];
`endif
            localparam int unsigned PIPE_MAX_VPORT_W = MAX_VPORT_RD_SLICE(VPORT_RD_W, PIPE_VPORT_IDX[i], PIPE_VPORT_CNT[i]);
            localparam int unsigned PIPE_MAX_VADDR_W = MAX_VPORT_RD_SLICE(VADDR_RD_W, PIPE_VPORT_IDX[i], PIPE_VPORT_CNT[i]);

            localparam bit [PIPE_VPORT_CNT[i]-1:0] PIPE_VPORT_BUFFER = {{(PIPE_VPORT_CNT[i]-1){1'b0}}, 1'b1};

            localparam int unsigned PIPE_MAX_WR_ATTEMPTS = MAX_WR_ATTEMPTS(i);

            logic [PIPE_VPORT_CNT[i]-1:0][4       :0] vreg_rd_addr;
            logic [PIPE_VPORT_CNT[i]-1:0][VREG_W-1:0] vreg_rd_data;
            always_comb begin
                vregfile_rd_addr[PIPE_VPORT_IDX[i]+PIPE_VPORT_CNT[i]-1:PIPE_VPORT_IDX[i]] = vreg_rd_addr[PIPE_VPORT_CNT[i]-1:0];
                for (int j = 0; j < PIPE_VPORT_CNT[i]; j++) begin
                    vreg_rd_data[j] = vregfile_rd_data[PIPE_VPORT_IDX[i] + j];
                end
            end

            // LSU-related signals
            vproc_xif #(
                .X_ID_WIDTH  ( XIF_ID_W  ),
                .X_MEM_WIDTH ( XIF_MEM_W )
            ) pipe_xif ();
            logic                pending_load, pending_store;
            logic                trans_complete_valid;
            logic                trans_complete_ready;
            logic [XIF_ID_W-1:0] trans_complete_id;
            logic                trans_complete_exc;
            logic [5:0]          trans_complete_exccode;

            // ELEM-related signals (for XREG writeback)
            logic                xreg_valid;
            logic                xreg_ready;
            logic [XIF_ID_W-1:0] xreg_id;
            logic [4:0]          xreg_addr;
            logic [31:0]         xreg_data;

            vproc_pipeline_wrapper #(
                .VREG_W                   ( VREG_W                     ),
                .CFG_VL_W                 ( CFG_VL_W                   ),
                .XIF_ID_W                 ( XIF_ID_W                   ),
                .XIF_ID_CNT               ( XIF_ID_CNT                 ),
                .UNITS                    ( PIPE_UNITS[i]              ),
                .MAX_VPORT_W              ( PIPE_MAX_VPORT_W           ),
                .MAX_VADDR_W              ( PIPE_MAX_VADDR_W           ),
                .VPORT_CNT                ( PIPE_VPORT_CNT[i]          ),
`ifdef VERILATOR
                // Workaround for Verilator due to https://github.com/verilator/verilator/issues/3433
                .VPORT_OFFSET             ( PIPE_VPORT_IDX[i]          ),
                .VREGFILE_VPORT_CNT       ( VPORT_RD_CNT               ),
                .VREGFILE_VPORT_W         ( VPORT_RD_W                 ),
                .VREGFILE_VADDR_W         ( VADDR_RD_W                 ),
`else
                .VPORT_W                  ( PIPE_VPORT_W               ),
                .VADDR_W                  ( PIPE_VADDR_W               ),
`endif
                .VPORT_BUFFER             ( PIPE_VPORT_BUFFER          ),
                .VPORT_V0                 ( 1'b1                       ),
                .MAX_OP_W                 ( PIPE_W[i]                  ),
                .VLSU_QUEUE_SZ            ( VLSU_QUEUE_SZ              ),
                .VLSU_FLAGS               ( VLSU_FLAGS                 ),
                .MUL_TYPE                 ( MUL_TYPE                   ),
                .MAX_WR_ATTEMPTS          ( PIPE_MAX_WR_ATTEMPTS       ),
                .DECODER_DATA_T           ( decoder_data               ),
                .DONT_CARE_ZERO           ( DONT_CARE_ZERO             )
            ) pipe (
                .clk_i                    ( clk_i                      ),
                .async_rst_ni             ( async_rst_n                ),
                .sync_rst_ni              ( sync_rst_n                 ),
                .pipe_in_valid_i          ( pipe_instr_valid[i]        ),
                .pipe_in_ready_o          ( pipe_instr_ready[i]        ),
                .pipe_in_data_i           ( pipe_instr_data            ),
                .vreg_pend_wr_i           ( pend_vreg_wr_map           ),
                .vreg_pend_rd_o           ( pipe_vreg_pend_rd_out[i]   ),
                .vreg_pend_rd_i           ( pipe_vreg_pend_rd_in [i]   ),
                .instr_spec_i             ( ~instr_notspec_q           ),
                .instr_killed_i           ( instr_killed_q             ),
                .instr_done_valid_o       ( instr_complete_valid[i]    ),
                .instr_done_id_o          ( instr_complete_id   [i]    ),
                .vreg_rd_addr_o           ( vreg_rd_addr               ),
                .vreg_rd_data_i           ( vreg_rd_data               ),
                .vreg_rd_v0_i             ( vreg_mask                  ),
                .vreg_wr_valid_o          ( pipe_vreg_wr_valid  [i]    ),
                .vreg_wr_ready_i          ( pipe_vreg_wr_ready  [i]    ),
                .vreg_wr_addr_o           ( pipe_vreg_wr_addr   [i]    ),
                .vreg_wr_be_o             ( pipe_vreg_wr_be     [i]    ),
                .vreg_wr_data_o           ( pipe_vreg_wr_data   [i]    ),
                .vreg_wr_clr_o            ( pipe_vreg_wr_clr    [i]    ),
                .vreg_wr_clr_cnt_o        ( pipe_vreg_wr_clr_cnt[i]    ),
                .pending_load_o           ( pending_load               ),
                .pending_store_o          ( pending_store              ),
                .xif_mem_if               ( pipe_xif                   ),
                .xif_memres_if            ( pipe_xif                   ),
                .trans_complete_valid_o   ( trans_complete_valid       ),
                .trans_complete_ready_i   ( trans_complete_ready       ),
                .trans_complete_id_o      ( trans_complete_id          ),
                .trans_complete_exc_o     ( trans_complete_exc         ),
                .trans_complete_exccode_o ( trans_complete_exccode     ),
                .xreg_valid_o             ( xreg_valid                 ),
                .xreg_ready_i             ( xreg_ready                 ),
                .xreg_id_o                ( xreg_id                    ),
                .xreg_addr_o              ( xreg_addr                  ),
                .xreg_data_o              ( xreg_data                  )
            );
            if (PIPE_UNITS[i][UNIT_LSU]) begin
                assign pending_load_lsu           = pending_load;
                assign pending_store_lsu          = pending_store;
                assign xif_mem_if.mem_valid       = pipe_xif.mem_valid;
                assign pipe_xif.mem_ready         = xif_mem_if.mem_ready;
                assign xif_mem_if.mem_req.id      = pipe_xif.mem_req.id;
                assign xif_mem_if.mem_req.addr    = pipe_xif.mem_req.addr;
                assign xif_mem_if.mem_req.mode    = pipe_xif.mem_req.mode;
                assign xif_mem_if.mem_req.we      = pipe_xif.mem_req.we;
                assign xif_mem_if.mem_req.be      = pipe_xif.mem_req.be;
                assign xif_mem_if.mem_req.wdata   = pipe_xif.mem_req.wdata;
                assign xif_mem_if.mem_req.last    = pipe_xif.mem_req.last;
                assign xif_mem_if.mem_req.spec    = pipe_xif.mem_req.spec;
                assign pipe_xif.mem_resp.exc      = xif_mem_if.mem_resp.exc;
                assign pipe_xif.mem_resp.exccode  = xif_mem_if.mem_resp.exccode;
                assign pipe_xif.mem_resp.dbg      = xif_mem_if.mem_resp.dbg;
                assign pipe_xif.mem_result_valid  = xif_memres_if.mem_result_valid;
                assign pipe_xif.mem_result.id     = xif_memres_if.mem_result.id;
                assign pipe_xif.mem_result.rdata  = xif_memres_if.mem_result.rdata;
                assign pipe_xif.mem_result.err    = xif_memres_if.mem_result.err;
                assign pipe_xif.mem_result.dbg    = xif_memres_if.mem_result.dbg;
                assign lsu_trans_complete_valid   = trans_complete_valid;
                assign trans_complete_ready       = lsu_trans_complete_ready;
                assign lsu_trans_complete_id      = trans_complete_id;
                assign lsu_trans_complete_exc     = trans_complete_exc;
                assign lsu_trans_complete_exccode = trans_complete_exccode;
            end
            if (PIPE_UNITS[i][UNIT_ELEM]) begin
                assign elem_xreg_valid = xreg_valid;
                assign xreg_ready      = elem_xreg_ready;
                assign elem_xreg_id    = xreg_id;
                assign elem_xreg_addr  = xreg_addr;
                assign elem_xreg_data  = xreg_data;
            end

        end
    endgenerate

    vproc_vreg_wr_mux #(
        .VREG_W             ( VREG_W             ),
        .VPORT_WR_CNT       ( VPORT_WR_CNT       ),
        .PIPE_CNT           ( PIPE_CNT           ),
        .PIPE_UNITS         ( PIPE_UNITS         ),
        .PIPE_VPORT_WR      ( PIPE_VPORT_WR      ),
        .STALL_PIPELINES    ( 1'b0               ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO     )
    ) vreg_wr_mux (
        .clk_i              ( clk_i              ),
        .async_rst_ni       ( async_rst_n        ),
        .sync_rst_ni        ( sync_rst_n         ),
        .vreg_wr_valid_i    ( pipe_vreg_wr_valid ),
        .vreg_wr_ready_o    ( pipe_vreg_wr_ready ),
        .vreg_wr_addr_i     ( pipe_vreg_wr_addr  ),
        .vreg_wr_be_i       ( pipe_vreg_wr_be    ),
        .vreg_wr_data_i     ( pipe_vreg_wr_data  ),
        .vreg_wr_clr_i      ( pipe_vreg_wr_clr     ),
        .vreg_wr_clr_cnt_i  ( pipe_vreg_wr_clr_cnt ),
        .pipe_clear_pend_vreg_wr_o ( pipe_clear_pend_vreg_wr ),
        .vregfile_wr_en_o   ( vregfile_wr_en_d   ),
        .vregfile_wr_addr_o ( vregfile_wr_addr_d ),
        .vregfile_wr_be_o   ( vregfile_wr_mask_d ),
        .vregfile_wr_data_o ( vregfile_wr_data_d )
    );


    ///////////////////////////////////////////////////////////////////////////
    // RESULT INTERFACE

    vproc_result #(
        .XIF_ID_W                  ( XIF_ID_W                   ),
        .DONT_CARE_ZERO            ( DONT_CARE_ZERO             )
    ) result_if (
        .clk_i                     ( clk_i                      ),
        .async_rst_ni              ( async_rst_n                ),
        .sync_rst_ni               ( sync_rst_n                 ),
        .result_empty_valid_i      ( result_empty_valid         ),
        .result_empty_id_i         ( result_empty_id            ),
        .result_lsu_valid_i        ( lsu_trans_complete_valid   ),
        .result_lsu_ready_o        ( lsu_trans_complete_ready   ),
        .result_lsu_id_i           ( lsu_trans_complete_id      ),
        .result_lsu_exc_i          ( lsu_trans_complete_exc     ),
        .result_lsu_exccode_i      ( lsu_trans_complete_exccode ),
        .result_xreg_valid_i       ( elem_xreg_valid            ),
        .result_xreg_ready_o       ( elem_xreg_ready            ),
        .result_xreg_id_i          ( elem_xreg_id               ),
        .result_xreg_addr_i        ( elem_xreg_addr             ),
        .result_xreg_data_i        ( elem_xreg_data             ),
        .result_csr_valid_i        ( result_csr_valid           ),
        .result_csr_ready_o        ( result_csr_ready           ),
        .result_csr_id_i           ( result_csr_id              ),
        .result_csr_addr_i         ( result_csr_addr            ),
        .result_csr_delayed_i      ( result_csr_delayed         ),
        .result_csr_data_i         ( result_csr_data            ),
        .result_csr_data_delayed_i ( csr_vl_o                   ),
        .xif_result_if             ( xif_result_if              )
    );

endmodule
