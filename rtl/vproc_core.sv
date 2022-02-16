// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_core #(
        parameter int unsigned        VREG_W         = 128,  // vector register width in bits
        parameter int unsigned        VMEM_W         = 32,   // vector memory interface width in bits
        parameter int unsigned        ALU_OP_W       = 64,   // ALU operand width in bits
        parameter int unsigned        MUL_OP_W       = 64,   // MUL unit operand width in bits
        parameter int unsigned        SLD_OP_W       = 64,   // SLD unit operand width in bits
        parameter int unsigned        GATHER_OP_W    = 32,   // ELEM unit GATHER operand width in bits
        parameter int unsigned        XIF_ID_W       = 3,    // width in bits of instruction IDs
        parameter int unsigned        QUEUE_SZ       = 2,    // instruction queue size
        parameter vproc_pkg::ram_type RAM_TYPE       = vproc_pkg::RAM_GENERIC,
        parameter vproc_pkg::mul_type MUL_TYPE       = vproc_pkg::MUL_GENERIC,
        parameter bit                 BUF_DEC        = 1'b1, // buffer decoder outputs
        parameter bit                 BUF_DEQUEUE    = 1'b1, // buffer instruction queue outputs
        parameter bit                 BUF_VREG_WR    = 1'b0,
        parameter bit                 BUF_VREG_PEND  = 1'b1, // buffer pending vreg reads
        parameter bit                 DONT_CARE_ZERO = 1'b0, // initialize don't care values to zero
        parameter bit                 ASYNC_RESET    = 1'b0  // set if rst_ni is an asynchronous reset
    )(
        input  logic                  clk_i,
        input  logic                  rst_ni,

        // eXtension interface
        vproc_xif.coproc_issue        xif_issue_if,
        vproc_xif.coproc_commit       xif_commit_if,
        vproc_xif.coproc_mem          xif_mem_if,
        vproc_xif.coproc_mem_result   xif_memres_if,
        vproc_xif.coproc_result       xif_result_if,

        output logic                  pending_load_o,
        output logic                  pending_store_o,

        // CSR connections
        output logic [31:0]           csr_vtype_o,
        output logic [31:0]           csr_vl_o,
        output logic [31:0]           csr_vlenb_o,
        output logic [31:0]           csr_vstart_o,
        input  logic [31:0]           csr_vstart_i,
        input  logic                  csr_vstart_set_i,
        output logic [1:0]            csr_vxrm_o,
        input  logic [1:0]            csr_vxrm_i,
        input  logic                  csr_vxrm_set_i,
        output logic                  csr_vxsat_o,
        input  logic                  csr_vxsat_i,
        input  logic                  csr_vxsat_set_i
    );

    import vproc_pkg::*;

    if ((VREG_W & (VREG_W - 1)) != 0 || VREG_W < 64) begin
        $fatal(1, "The vector register width VREG_W must be at least 64 and a power of two.  ",
                  "The current value of %d is invalid.", VREG_W);
    end

    localparam int unsigned VMSK_W = VREG_W / 8;   // single register mask size

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
            vxrm_q     <= VXRM_RNU;
            vxsat_q    <= 1'b0;
        end else begin
            vsew_q     <= vsew_d;
            lmul_q     <= lmul_d;
            agnostic_q <= agnostic_d;
            vl_0_q     <= vl_0_d;
            vl_q       <= vl_d;
            vl_csr_q   <= vl_csr_d;
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

    // CSR writes
    always_comb begin
        vxrm_d = vxrm_q;
        if (csr_vxrm_set_i) begin
            unique case (csr_vxrm_i)
                2'b00: vxrm_d = VXRM_RNU;
                2'b01: vxrm_d = VXRM_RNE;
                2'b10: vxrm_d = VXRM_RDN;
                2'b11: vxrm_d = VXRM_ROD;
                default: ;
            endcase
        end
    end
    assign vxsat_d = csr_vxsat_set_i ? csr_vxsat_i : vxsat_q;


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

    logic   instr_illegal;
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
        .illegal_o      ( instr_illegal                ),
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

    logic                instr_complete_valid[5];
    logic [XIF_ID_W-1:0] instr_complete_id   [5];

    // return an empty result or VL as result
    logic                result_empty_valid, result_vl_valid;
    logic                                    result_vl_ready;
    logic [XIF_ID_W-1:0] result_empty_id,    result_vl_id;
    logic [4:0]                              result_vl_addr;

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
        result_vl_valid    = 1'b0;
        result_vl_id       = dec_data_q.id;
        result_vl_addr     = dec_data_q.rd.addr;
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

            if (dec_buf_valid_q & (dec_data_q.unit == UNIT_CFG) & (dec_data_q.id == xif_commit_if.commit.id) & result_vl_ready) begin
                // vset[i]vl[i] instructions are not enqueued.  The instruction
                // is retired and the result returned as soon as it is
                // committed.
                dec_clear       = 1'b1;
                result_vl_valid = ~xif_commit_if.commit.commit_kill;
            end else begin
                instr_notspec_d[xif_commit_if.commit.id] = 1'b1;
            end

            instr_killed_d[xif_commit_if.commit.id] = xif_commit_if.commit.commit_kill;
        end
        if (dec_buf_valid_q & (dec_data_q.unit == UNIT_CFG) & instr_notspec_q[dec_data_q.id]) begin
            // Execute a vset[i]vl[i] instruction that has already been
            // committed earlier (i.e., while decoding and accepting the
            // instruction).
            dec_clear                      = result_vl_ready;
            result_vl_valid                = ~instr_killed_q[dec_data_q.id];
            instr_notspec_d[dec_data_q.id] = 1'b0;
        end
        for (int i = 0; i < 5; i++) begin
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

    // update configuration state for vset[i]vl[i] instructions
    always_comb begin
        vsew_d     = vsew_q;
        lmul_d     = lmul_q;
        agnostic_d = agnostic_q;
        vl_0_d     = vl_0_q;
        vl_d       = vl_q;
        vl_csr_d   = vl_csr_q;
        if (result_vl_valid) begin
            vsew_d     = dec_data_q.mode.cfg.vsew;
            lmul_d     = dec_data_q.mode.cfg.lmul;
            agnostic_d = dec_data_q.mode.cfg.agnostic;
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
            if ((dec_data_q.rs1.r.xval == 32'b0) & ~dec_data_q.mode.cfg.vlmax) begin
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
        if (BUF_DEQUEUE) begin
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
        if (QUEUE_SZ > 0) begin
            vproc_queue #(
                .WIDTH        ( $bits(decoder_data)     ),
                .DEPTH        ( QUEUE_SZ                )
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

    // hazard state
    logic [31:0] vreg_wr_hazard_map_q;     // active vregs
    logic [31:0] vreg_wr_hazard_map_set;   // add active regs (via decode)
    logic [31:0] vreg_wr_hazard_map_clr;   // remove active regs (via ex units)
    always_ff @(posedge clk_i or negedge async_rst_n) begin : vproc_hazard_reg
        if (~async_rst_n) begin
            vreg_wr_hazard_map_q <= 32'b0;
        end
        else if (~sync_rst_n) begin
            vreg_wr_hazard_map_q <= 32'b0;
        end else begin
            vreg_wr_hazard_map_q <= (vreg_wr_hazard_map_q & (~vreg_wr_hazard_map_clr)) |
                                     vreg_wr_hazard_map_set;
        end
    end

    // pending hazards of next instruction (in dequeue buffer)
    logic pending_hazards;
    assign pending_hazards = (queue_pending_wr_q & vreg_wr_hazard_map_q) != 32'b0;

    // instruction ready and acknowledge signals for each unit:
    logic op_rdy_lsu,  op_ack_lsu;
    logic op_rdy_alu,  op_ack_alu;
    logic op_rdy_mul,  op_ack_mul;
    logic op_rdy_sld,  op_ack_sld;
    logic op_rdy_elem, op_ack_elem;
    always_comb begin
        op_rdy_lsu  = 1'b0;
        op_rdy_alu  = 1'b0;
        op_rdy_mul  = 1'b0;
        op_rdy_sld  = 1'b0;
        op_rdy_elem = 1'b0;
        // hold back ready signal until hazards are cleared:
        if (queue_valid_q && ~pending_hazards) begin
            unique case (queue_data_q.unit)
                UNIT_LSU:  op_rdy_lsu  = 1'b1;
                UNIT_ALU:  op_rdy_alu  = 1'b1;
                UNIT_MUL:  op_rdy_mul  = 1'b1;
                UNIT_SLD:  op_rdy_sld  = 1'b1;
                UNIT_ELEM: op_rdy_elem = 1'b1;
                default: ;
            endcase
        end
    end
    always_comb begin
        op_ack                 = 1'b0;
        vreg_wr_hazard_map_set = '0;
        if ((op_rdy_lsu  & op_ack_lsu ) |
            (op_rdy_alu  & op_ack_alu ) |
            (op_rdy_mul  & op_ack_mul ) |
            (op_rdy_sld  & op_ack_sld ) |
            (op_rdy_elem & op_ack_elem)) begin
            op_ack              = 1'b1;
            vreg_wr_hazard_map_set = queue_pending_wr_q;
        end
    end

    // vreg hazard clearing:
    logic [31:0] vreg_wr_hazard_clr_lsu;
    logic [31:0] vreg_wr_hazard_clr_alu;
    logic [31:0] vreg_wr_hazard_clr_mul;
    logic [31:0] vreg_wr_hazard_clr_sld;
    logic [31:0] vreg_wr_hazard_clr_elem;
    assign vreg_wr_hazard_map_clr = vreg_wr_hazard_clr_lsu  |
                                    vreg_wr_hazard_clr_alu  |
                                    vreg_wr_hazard_clr_mul  |
                                    vreg_wr_hazard_clr_sld  |
                                    vreg_wr_hazard_clr_elem;


    ///////////////////////////////////////////////////////////////////////////
    // REGISTER FILE AND EXECUTION UNITS

    // register file:
    logic              vregfile_wr_en_q  [2], vregfile_wr_en_d  [2];
    logic [4:0]        vregfile_wr_addr_q[2], vregfile_wr_addr_d[2];
    logic [VREG_W-1:0] vregfile_wr_data_q[2], vregfile_wr_data_d[2];
    logic [VMSK_W-1:0] vregfile_wr_mask_q[2], vregfile_wr_mask_d[2];
    logic [4:0]        vregfile_rd_addr[7];
    logic [VREG_W-1:0] vregfile_rd_data[7];
    vproc_vregfile #(
        .VREG_W       ( VREG_W             ),
        .PORT_W       ( VREG_W             ),
        .PORTS_RD     ( 7                  ),
        .PORTS_WR     ( 2                  ),
        .RAM_TYPE     ( RAM_TYPE           )
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
        if (BUF_VREG_WR) begin
            always_ff @(posedge clk_i) begin
                for (int i = 0; i < 2; i++) begin
                    vregfile_wr_en_q  [i] <= vregfile_wr_en_d  [i];
                    vregfile_wr_addr_q[i] <= vregfile_wr_addr_d[i];
                    vregfile_wr_data_q[i] <= vregfile_wr_data_d[i];
                    vregfile_wr_mask_q[i] <= vregfile_wr_mask_d[i];
                end
            end
        end else begin
            always_comb begin
                for (int i = 0; i < 2; i++) begin
                    vregfile_wr_en_q  [i] = vregfile_wr_en_d  [i];
                    vregfile_wr_addr_q[i] = vregfile_wr_addr_d[i];
                    vregfile_wr_data_q[i] = vregfile_wr_data_d[i];
                    vregfile_wr_mask_q[i] = vregfile_wr_mask_d[i];
                end
            end
        end
    endgenerate


    // Pending reads
    logic [31:0] vreg_pend_rd_by_lsu_q, vreg_pend_rd_by_alu_q, vreg_pend_rd_by_mul_q, vreg_pend_rd_by_sld_q, vreg_pend_rd_by_elem_q;
    logic [31:0] vreg_pend_rd_by_lsu_d, vreg_pend_rd_by_alu_d, vreg_pend_rd_by_mul_d, vreg_pend_rd_by_sld_d, vreg_pend_rd_by_elem_d;
    logic [31:0] vreg_pend_rd_to_lsu_q, vreg_pend_rd_to_alu_q, vreg_pend_rd_to_mul_q, vreg_pend_rd_to_sld_q, vreg_pend_rd_to_elem_q;
    logic [31:0] vreg_pend_rd_to_lsu_d, vreg_pend_rd_to_alu_d, vreg_pend_rd_to_mul_d, vreg_pend_rd_to_sld_d, vreg_pend_rd_to_elem_d;
    generate
        if (BUF_VREG_PEND) begin
            // Note: A vreg write cannot happen within the first two cycles of
            // an instruction, hence delaying the pending vreg reads signals by
            // two cycles should cause no issues. This adds two unnecessary
            // extra stall cycles in case a write is blocked by a pending read
            // but that should happen rarely anyways.
            always_ff @(posedge clk_i) begin
                vreg_pend_rd_by_lsu_q  <= vreg_pend_rd_by_lsu_d;
                vreg_pend_rd_by_alu_q  <= vreg_pend_rd_by_alu_d;
                vreg_pend_rd_by_mul_q  <= vreg_pend_rd_by_mul_d;
                vreg_pend_rd_by_sld_q  <= vreg_pend_rd_by_sld_d;
                vreg_pend_rd_by_elem_q <= vreg_pend_rd_by_elem_d;
                vreg_pend_rd_to_lsu_q  <= vreg_pend_rd_to_lsu_d;
                vreg_pend_rd_to_alu_q  <= vreg_pend_rd_to_alu_d;
                vreg_pend_rd_to_mul_q  <= vreg_pend_rd_to_mul_d;
                vreg_pend_rd_to_sld_q  <= vreg_pend_rd_to_sld_d;
                vreg_pend_rd_to_elem_q <= vreg_pend_rd_to_elem_d;
            end
        end else begin
            assign vreg_pend_rd_by_lsu_q  = vreg_pend_rd_by_lsu_d;
            assign vreg_pend_rd_by_alu_q  = vreg_pend_rd_by_alu_d;
            assign vreg_pend_rd_by_mul_q  = vreg_pend_rd_by_mul_d;
            assign vreg_pend_rd_by_sld_q  = vreg_pend_rd_by_sld_d;
            assign vreg_pend_rd_by_elem_q = vreg_pend_rd_by_elem_d;
            assign vreg_pend_rd_to_lsu_q  = vreg_pend_rd_to_lsu_d;
            assign vreg_pend_rd_to_alu_q  = vreg_pend_rd_to_alu_d;
            assign vreg_pend_rd_to_mul_q  = vreg_pend_rd_to_mul_d;
            assign vreg_pend_rd_to_sld_q  = vreg_pend_rd_to_sld_d;
            assign vreg_pend_rd_to_elem_q = vreg_pend_rd_to_elem_d;
        end
    endgenerate
    assign vreg_pend_rd_to_lsu_d  = vreg_pend_rd_by_alu_q | vreg_pend_rd_by_mul_q | vreg_pend_rd_by_sld_q | vreg_pend_rd_by_elem_q;
    assign vreg_pend_rd_to_alu_d  = vreg_pend_rd_by_lsu_q | vreg_pend_rd_by_mul_q | vreg_pend_rd_by_sld_q | vreg_pend_rd_by_elem_q;
    assign vreg_pend_rd_to_mul_d  = vreg_pend_rd_by_lsu_q | vreg_pend_rd_by_alu_q | vreg_pend_rd_by_sld_q | vreg_pend_rd_by_elem_q;
    assign vreg_pend_rd_to_sld_d  = vreg_pend_rd_by_lsu_q | vreg_pend_rd_by_alu_q | vreg_pend_rd_by_mul_q | vreg_pend_rd_by_elem_q;
    assign vreg_pend_rd_to_elem_d = vreg_pend_rd_by_lsu_q | vreg_pend_rd_by_alu_q | vreg_pend_rd_by_mul_q | vreg_pend_rd_by_sld_q;


    // LSU
    logic                misaligned_lsu;
    logic [VREG_W-1:0]   lsu_wr_data;
    logic [VMSK_W-1:0]   lsu_wr_mask;
    logic [4:0]          lsu_wr_addr;
    logic                lsu_wr_en;
    logic                lsu_trans_complete_valid;
    logic [XIF_ID_W-1:0] lsu_trans_complete_id;
    logic                lsu_trans_complete_exc;
    logic [5:0]          lsu_trans_complete_exccode;
    vproc_lsu #(
        .VREG_W                   ( VREG_W                        ),
        .VMSK_W                   ( VMSK_W                        ),
        .VMEM_W                   ( VMEM_W                        ),
        .CFG_VL_W                 ( CFG_VL_W                      ),
        .XIF_ID_W                 ( XIF_ID_W                      ),
        .XIF_ID_CNT               ( XIF_ID_CNT                    ),
        .MAX_WR_ATTEMPTS          ( 1                             ),
        .DONT_CARE_ZERO           ( DONT_CARE_ZERO                )
    ) lsu (
        .clk_i                    ( clk_i                         ),
        .async_rst_ni             ( async_rst_n                   ),
        .sync_rst_ni              ( sync_rst_n                    ),
        .id_i                     ( queue_data_q.id               ),
        .vsew_i                   ( queue_data_q.vsew             ),
        .emul_i                   ( queue_data_q.emul             ),
        .vl_i                     ( queue_data_q.vl               ),
        .vl_0_i                   ( queue_data_q.vl_0             ),
        .op_rdy_i                 ( op_rdy_lsu                    ),
        .op_ack_o                 ( op_ack_lsu                    ),
        .misaligned_o             ( misaligned_lsu                ),
        .mode_i                   ( queue_data_q.mode.lsu         ),
        .rs1_i                    ( queue_data_q.rs1              ),
        .rs2_i                    ( queue_data_q.rs2              ),
        .vd_i                     ( queue_data_q.rd.addr          ),
        .vreg_pend_wr_i           ( vreg_wr_hazard_map_q          ),
        .vreg_pend_rd_o           ( vreg_pend_rd_by_lsu_d         ),
        .vreg_pend_rd_i           ( vreg_pend_rd_to_lsu_q         ),
        .pending_load_o           ( pending_load_lsu              ),
        .pending_store_o          ( pending_store_lsu             ),
        .clear_wr_hazards_o       ( vreg_wr_hazard_clr_lsu        ),
        .instr_spec_i             ( ~instr_notspec_q              ),
        .instr_killed_i           ( instr_killed_q                ),
        .instr_done_valid_o       ( instr_complete_valid[0]       ),
        .instr_done_id_o          ( instr_complete_id   [0]       ),
        .trans_complete_valid_o   ( lsu_trans_complete_valid      ),
        .trans_complete_id_o      ( lsu_trans_complete_id         ),
        .trans_complete_exc_o     ( lsu_trans_complete_exc        ),
        .trans_complete_exccode_o ( lsu_trans_complete_exccode    ),
        .vreg_mask_i              ( vreg_mask                     ),
        .vreg_rd_i                ( vregfile_rd_data[1]           ),
        .vreg_rd_addr_o           ( vregfile_rd_addr[1]           ),
        .vreg_wr_o                ( lsu_wr_data                   ),
        .vreg_wr_addr_o           ( lsu_wr_addr                   ),
        .vreg_wr_mask_o           ( lsu_wr_mask                   ),
        .vreg_wr_en_o             ( lsu_wr_en                     ),
        .xif_mem_if               ( xif_mem_if                    ),
        .xif_memres_if            ( xif_memres_if                 )
    );


    // ALU
    logic [VREG_W-1:0] alu_wr_data;
    logic [VMSK_W-1:0] alu_wr_mask;
    logic [4:0]        alu_wr_addr;
    logic              alu_wr_en;
    vproc_pipeline #(
        .VREG_W             ( VREG_W                        ),
        .VMSK_W             ( VMSK_W                        ),
        .CFG_VL_W           ( CFG_VL_W                      ),
        .XIF_ID_W           ( XIF_ID_W                      ),
        .XIF_ID_CNT         ( XIF_ID_CNT                    ),
        .UNIT               ( UNIT_ALU                      ),
        .OP_W               ( ALU_OP_W                      ),
        .MAX_WR_ATTEMPTS    ( 2                             ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO                )
    ) alu (
        .clk_i              ( clk_i                         ),
        .async_rst_ni       ( async_rst_n                   ),
        .sync_rst_ni        ( sync_rst_n                    ),
        .id_i               ( queue_data_q.id               ),
        .vsew_i             ( queue_data_q.vsew             ),
        .emul_i             ( queue_data_q.emul             ),
        .vxrm_i             ( queue_data_q.vxrm             ),
        .vl_i               ( queue_data_q.vl               ),
        .vl_0_i             ( queue_data_q.vl_0             ),
        .op_rdy_i           ( op_rdy_alu                    ),
        .op_ack_o           ( op_ack_alu                    ),
        .mode_i             ( queue_data_q.mode             ),
        .widenarrow_i       ( queue_data_q.widenarrow       ),
        .rs1_i              ( queue_data_q.rs1              ),
        .rs2_i              ( queue_data_q.rs2              ),
        .vd_i               ( queue_data_q.rd.addr          ),
        .vreg_pend_wr_i     ( vreg_wr_hazard_map_q          ),
        .vreg_pend_rd_o     ( vreg_pend_rd_by_alu_d         ),
        .vreg_pend_rd_i     ( vreg_pend_rd_to_alu_q         ),
        .clear_wr_hazards_o ( vreg_wr_hazard_clr_alu        ),
        .instr_spec_i       ( ~instr_notspec_q              ),
        .instr_killed_i     ( instr_killed_q                ),
        .instr_done_valid_o ( instr_complete_valid[1]       ),
        .instr_done_id_o    ( instr_complete_id   [1]       ),
        .vreg_mask_i        ( vreg_mask                     ),
        .vreg_rd_i          ( vregfile_rd_data[2]           ),
        .vreg_rd_addr_o     ( vregfile_rd_addr[2]           ),
        .vreg_wr_o          ( alu_wr_data                   ),
        .vreg_wr_addr_o     ( alu_wr_addr                   ),
        .vreg_wr_mask_o     ( alu_wr_mask                   ),
        .vreg_wr_en_o       ( alu_wr_en                     )
    );


    // MUL
    logic [VREG_W-1:0] mul_wr_data;
    logic [VMSK_W-1:0] mul_wr_mask;
    logic [4:0]        mul_wr_addr;
    logic              mul_wr_en;
    vproc_mul #(
        .VREG_W             ( VREG_W                                 ),
        .VMSK_W             ( VMSK_W                                 ),
        .CFG_VL_W           ( CFG_VL_W                               ),
        .MUL_OP_W           ( MUL_OP_W                               ),
        .XIF_ID_W           ( XIF_ID_W                               ),
        .XIF_ID_CNT         ( XIF_ID_CNT                             ),
        .MAX_WR_ATTEMPTS    ( 1                                      ),
        .MUL_TYPE           ( MUL_TYPE                               ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO                         )
    ) mul (
        .clk_i              ( clk_i                                  ),
        .async_rst_ni       ( async_rst_n                            ),
        .sync_rst_ni        ( sync_rst_n                             ),
        .id_i               ( queue_data_q.id                        ),
        .vsew_i             ( queue_data_q.vsew                      ),
        .emul_i             ( queue_data_q.emul                      ),
        .vxrm_i             ( queue_data_q.vxrm                      ),
        .vl_i               ( queue_data_q.vl                        ),
        .vl_0_i             ( queue_data_q.vl_0                      ),
        .op_rdy_i           ( op_rdy_mul                             ),
        .op_ack_o           ( op_ack_mul                             ),
        .mode_i             ( queue_data_q.mode.mul                  ),
        .widening_i         ( queue_data_q.widenarrow == OP_WIDENING ),
        .rs1_i              ( queue_data_q.rs1                       ),
        .rs2_i              ( queue_data_q.rs2                       ),
        .vd_i               ( queue_data_q.rd.addr                   ),
        .vreg_pend_wr_i     ( vreg_wr_hazard_map_q                   ),
        .vreg_pend_rd_o     ( vreg_pend_rd_by_mul_d                  ),
        .vreg_pend_rd_i     ( vreg_pend_rd_to_mul_q                  ),
        .clear_wr_hazards_o ( vreg_wr_hazard_clr_mul                 ),
        .instr_spec_i       ( ~instr_notspec_q                       ),
        .instr_killed_i     ( instr_killed_q                         ),
        .instr_done_valid_o ( instr_complete_valid[2]                ),
        .instr_done_id_o    ( instr_complete_id   [2]                ),
        .vreg_mask_i        ( vreg_mask                              ),
        .vreg_rd_i          ( vregfile_rd_data[3]                    ),
        .vreg_rd3_i         ( vregfile_rd_data[4]                    ),
        .vreg_rd_addr_o     ( vregfile_rd_addr[3]                    ),
        .vreg_rd3_addr_o    ( vregfile_rd_addr[4]                    ),
        .vreg_wr_o          ( mul_wr_data                            ),
        .vreg_wr_addr_o     ( mul_wr_addr                            ),
        .vreg_wr_mask_o     ( mul_wr_mask                            ),
        .vreg_wr_en_o       ( mul_wr_en                              )
    );


    // SLD unit
    logic [VREG_W-1:0] sld_wr_data;
    logic [VMSK_W-1:0] sld_wr_mask;
    logic [4:0]        sld_wr_addr;
    logic              sld_wr_en;
    vproc_sld #(
        .VREG_W             ( VREG_W                   ),
        .VMSK_W             ( VMSK_W                   ),
        .CFG_VL_W           ( CFG_VL_W                 ),
        .SLD_OP_W           ( SLD_OP_W                 ),
        .XIF_ID_W           ( XIF_ID_W                 ),
        .XIF_ID_CNT         ( XIF_ID_CNT               ),
        .MAX_WR_ATTEMPTS    ( 2                        ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO           )
    ) sld (
        .clk_i              ( clk_i                    ),
        .async_rst_ni       ( async_rst_n              ),
        .sync_rst_ni        ( sync_rst_n               ),
        .id_i               ( queue_data_q.id          ),
        .vsew_i             ( queue_data_q.vsew        ),
        .emul_i             ( queue_data_q.emul        ),
        .vl_i               ( queue_data_q.vl          ),
        .vl_0_i             ( queue_data_q.vl_0        ),
        .op_rdy_i           ( op_rdy_sld               ),
        .op_ack_o           ( op_ack_sld               ),
        .mode_i             ( queue_data_q.mode.sld    ),
        .rs1_i              ( queue_data_q.rs1         ),
        .rs2_i              ( queue_data_q.rs2         ),
        .vd_i               ( queue_data_q.rd.addr     ),
        .vreg_pend_wr_i     ( vreg_wr_hazard_map_q     ),
        .vreg_pend_rd_o     ( vreg_pend_rd_by_sld_d    ),
        .vreg_pend_rd_i     ( vreg_pend_rd_to_sld_q    ),
        .clear_wr_hazards_o ( vreg_wr_hazard_clr_sld   ),
        .instr_spec_i       ( ~instr_notspec_q         ),
        .instr_killed_i     ( instr_killed_q           ),
        .instr_done_valid_o ( instr_complete_valid[3]  ),
        .instr_done_id_o    ( instr_complete_id   [3]  ),
        .vreg_mask_i        ( vreg_mask                ),
        .vreg_rd_i          ( vregfile_rd_data[5]      ),
        .vreg_rd_addr_o     ( vregfile_rd_addr[5]      ),
        .vreg_wr_o          ( sld_wr_data              ),
        .vreg_wr_addr_o     ( sld_wr_addr              ),
        .vreg_wr_mask_o     ( sld_wr_mask              ),
        .vreg_wr_en_o       ( sld_wr_en                )
    );


    // ELEM unit
    logic [VREG_W-1:0]   elem_wr_data;
    logic [VMSK_W-1:0]   elem_wr_mask;
    logic [4:0]          elem_wr_addr;
    logic                elem_wr_en;
    logic                elem_xreg_valid;
    logic [XIF_ID_W-1:0] elem_xreg_id;
    logic [4:0]          elem_xreg_addr;
    logic [31:0]         elem_xreg_data;
    vproc_elem #(
        .VREG_W             ( VREG_W                   ),
        .VMSK_W             ( VMSK_W                   ),
        .CFG_VL_W           ( CFG_VL_W                 ),
        .GATHER_OP_W        ( GATHER_OP_W              ),
        .XIF_ID_W           ( XIF_ID_W                 ),
        .XIF_ID_CNT         ( XIF_ID_CNT               ),
        .MAX_WR_ATTEMPTS    ( 3                        ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO           )
    ) elem (
        .clk_i              ( clk_i                    ),
        .async_rst_ni       ( async_rst_n              ),
        .sync_rst_ni        ( sync_rst_n               ),
        .id_i               ( queue_data_q.id          ),
        .vsew_i             ( queue_data_q.vsew        ),
        .emul_i             ( queue_data_q.emul        ),
        .vl_i               ( queue_data_q.vl          ),
        .vl_0_i             ( queue_data_q.vl_0        ),
        .op_rdy_i           ( op_rdy_elem              ),
        .op_ack_o           ( op_ack_elem              ),
        .mode_i             ( queue_data_q.mode.elem   ),
        .widenarrow_i       ( queue_data_q.widenarrow  ),
        .rs1_i              ( queue_data_q.rs1         ),
        .rs2_i              ( queue_data_q.rs2         ),
        .vd_i               ( queue_data_q.rd.addr     ),
        .vreg_pend_wr_i     ( vreg_wr_hazard_map_q     ),
        .vreg_pend_rd_o     ( vreg_pend_rd_by_elem_d   ),
        .vreg_pend_rd_i     ( vreg_pend_rd_to_elem_q   ),
        .clear_wr_hazards_o ( vreg_wr_hazard_clr_elem  ),
        .instr_spec_i       ( ~instr_notspec_q         ),
        .instr_killed_i     ( instr_killed_q           ),
        .instr_done_valid_o ( instr_complete_valid[4]  ),
        .instr_done_id_o    ( instr_complete_id   [4]  ),
        .vreg_mask_i        ( vreg_mask                ),
        .vreg_rd_i          ( vregfile_rd_data[6]      ),
        .vreg_rd_addr_o     ( vregfile_rd_addr[6]      ),
        .vreg_wr_o          ( elem_wr_data             ),
        .vreg_wr_addr_o     ( elem_wr_addr             ),
        .vreg_wr_mask_o     ( elem_wr_mask             ),
        .vreg_wr_en_o       ( elem_wr_en               ),
        .xreg_valid_o       ( elem_xreg_valid          ),
        .xreg_id_o          ( elem_xreg_id             ),
        .xreg_addr_o        ( elem_xreg_addr           ),
        .xreg_data_o        ( elem_xreg_data           )
    );


    // LSU/ALU/ELEM write multiplexer:
    always_comb begin
        vregfile_wr_en_d  [0] = lsu_wr_en | alu_wr_en | elem_wr_en;
        vregfile_wr_addr_d[0] = lsu_wr_en ? lsu_wr_addr : (alu_wr_en ? alu_wr_addr : elem_wr_addr);
        vregfile_wr_data_d[0] = lsu_wr_en ? lsu_wr_data : (alu_wr_en ? alu_wr_data : elem_wr_data);
        vregfile_wr_mask_d[0] = lsu_wr_en ? lsu_wr_mask : (alu_wr_en ? alu_wr_mask : elem_wr_mask);
    end


    // MUL/SLD write multiplexer:
    always_comb begin
        vregfile_wr_en_d  [1] = mul_wr_en | sld_wr_en;
        vregfile_wr_addr_d[1] = mul_wr_en ? mul_wr_addr : sld_wr_addr;
        vregfile_wr_data_d[1] = mul_wr_en ? mul_wr_data : sld_wr_data;
        vregfile_wr_mask_d[1] = mul_wr_en ? mul_wr_mask : sld_wr_mask;
    end


    ///////////////////////////////////////////////////////////////////////////
    // RESULT INTERFACE

    vproc_result #(
        .XIF_ID_W             ( XIF_ID_W                   ),
        .DONT_CARE_ZERO       ( DONT_CARE_ZERO             )
    ) result_if (
        .clk_i                ( clk_i                      ),
        .async_rst_ni         ( async_rst_n                ),
        .sync_rst_ni          ( sync_rst_n                 ),
        .result_lsu_valid_i   ( lsu_trans_complete_valid   ),
        .result_lsu_id_i      ( lsu_trans_complete_id      ),
        .result_lsu_exc_i     ( lsu_trans_complete_exc     ),
        .result_lsu_exccode_i ( lsu_trans_complete_exccode ),
        .result_xreg_valid_i  ( elem_xreg_valid            ),
        .result_xreg_id_i     ( elem_xreg_id               ),
        .result_xreg_addr_i   ( elem_xreg_addr             ),
        .result_xreg_data_i   ( elem_xreg_data             ),
        .result_empty_valid_i ( result_empty_valid         ),
        .result_empty_ready_o (                            ),
        .result_empty_id_i    ( result_empty_id            ),
        .result_vl_valid_i    ( result_vl_valid            ),
        .result_vl_ready_o    ( result_vl_ready            ),
        .result_vl_id_i       ( result_vl_id               ),
        .result_vl_addr_i     ( result_vl_addr             ),
        .result_vl_data_i     ( csr_vl_o                   ),
        .xif_result_if        ( xif_result_if              )
    );

endmodule
