// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


module vproc_core #(
        parameter int unsigned        VREG_W         = 128,  // vector register width in bits
        parameter int unsigned        VMEM_W         = 32,   // vector memory interface width in bits
        parameter int unsigned        ALU_OP_W       = 64,   // ALU operand width in bits
        parameter int unsigned        MUL_OP_W       = 64,   // MUL unit operand width in bits
        parameter int unsigned        SLD_OP_W       = 64,   // SLD unit operand width in bits
        parameter int unsigned        GATHER_OP_W    = 32,   // ELEM unit GATHER operand width in bits
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

        input  logic                  instr_valid_i,
        input  logic [31:0]           instr_i,
        input  logic                  x_rs1_valid_i,
        input  logic [31:0]           x_rs1_i,          // value of x register rs1
        input  logic                  x_rs2_valid_i,
        input  logic [31:0]           x_rs2_i,          // value of x register rs2

        output logic                  instr_gnt_o,      // grant instructions
        output logic                  instr_illegal_o,  // illegal instruction flag
        output logic                  misaligned_ls_o,  // misaligned load/store
        output logic                  xreg_wait_o,      // main processor shall wait for result

        input  logic                  instr_commit_i,   // commit the previous instruction
        input  logic                  instr_kill_i,     // kill the previous instruction

        input  logic                  result_ready_i,   // host is ready to accept the result
        output logic                  result_valid_o,
        output logic                  xreg_valid_o,
        output logic [31:0]           xreg_o,           // value to be written to destination x register

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
        input  logic                  csr_vxsat_set_i,

        // vector memory interface
        output logic                  data_req_o,
        input  logic                  data_gnt_i,
        input  logic                  data_rvalid_i,
        input  logic                  data_err_i,
        input  logic [VMEM_W-1:0]     data_rdata_i,
        output logic [31:0]           data_addr_o,
        output logic                  data_we_o,
        output logic [(VMEM_W/8)-1:0] data_be_o,
        output logic [VMEM_W-1:0]     data_wdata_o
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
    assign csr_vl_o     = {{(32-CFG_VL_W-1){1'b0}}, vl_csr_q};
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
        cfg_vsew             vsew;
        cfg_lmul             lmul;
        logic                vl_0;
        logic [CFG_VL_W-1:0] vl;
        op_unit              unit;
        op_mode              mode;
        op_widenarrow        widenarrow;
        op_regs              rs1;
        op_regs              rs2;
        op_regd              rd;
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

    vproc_decoder #(
        .DONT_CARE_ZERO ( DONT_CARE_ZERO        )
    ) dec (
        .instr_i        ( instr_i               ),
        .instr_valid_i  ( instr_valid_i         ),
        .x_rs1_i        ( x_rs1_i               ),
        .x_rs2_i        ( x_rs2_i               ),
        .vsew_i         ( vsew_q                ),
        .lmul_i         ( lmul_q                ),
        .vxrm_i         ( vxrm_q                ),
        .illegal_o      ( instr_illegal_o       ),
        .valid_o        ( dec_valid             ),
        .lmul_o         ( dec_data_d.lmul       ),
        .unit_o         ( dec_data_d.unit       ),
        .mode_o         ( dec_data_d.mode       ),
        .widenarrow_o   ( dec_data_d.widenarrow ),
        .rs1_o          ( dec_data_d.rs1        ),
        .rs2_o          ( dec_data_d.rs2        ),
        .rd_o           ( dec_data_d.rd         )
    );
    assign dec_data_d.vsew = vsew_q;
    assign dec_data_d.vl_0 = vl_0_q;
    assign dec_data_d.vl   = vl_q;

    assign instr_gnt_o = instr_valid_i & (instr_illegal_o | (dec_valid & dec_ready));
    assign xreg_wait_o = ((dec_data_d.unit == UNIT_ELEM) & dec_data_d.mode.elem.xreg) | (dec_data_d.unit == UNIT_CFG);


    ///////////////////////////////////////////////////////////////////////////
    // INSTRUCTION COMMIT STAGE

    // track whether the host has commited or killed the instruction in the decode buffer
    // TODO: assumption: instr_commit_i and instr_kill_i are not asserted simultaneously
    logic dec_committed_q, dec_committed_d;
    logic dec_killed_q,    dec_killed_d;
    always_ff @(posedge clk_i or negedge async_rst_n) begin : vproc_commit_buf
        if (~async_rst_n) begin
            dec_committed_q <= 1'b0;
            dec_killed_q    <= 1'b0;
        end
        else if (~sync_rst_n) begin
            dec_committed_q <= 1'b0;
            dec_killed_q    <= 1'b0;
        end else begin
            dec_committed_q <= dec_committed_d;
            dec_killed_q    <= dec_killed_d;
        end
    end
    // instr_commit_i (or instr_kill_i) can either refer to the instruction currently held in the
    // decode buffer or to the next instruction to enter the decode buffer if the current instr is
    // moving on (dec_ready is asserted); however the latter is only true if the current instr has
    // already been committed/killed or if the buffer is currently empty (i.e., ~dec_buf_valid_q)
    assign dec_committed_d = dec_ready ? (~dec_buf_valid_q | dec_committed_q) & instr_commit_i : dec_committed_q | instr_commit_i;
    assign dec_killed_d    = dec_ready ? (~dec_buf_valid_q | dec_killed_q   ) & instr_kill_i   : dec_killed_q    | instr_kill_i  ;

    logic queue_ready,  queue_push; // instruction queue ready and push signals (enqueue handshake)
    logic result_empty, result_vl;  // return an empty result or VL as result
    always_comb begin
        queue_push = 1'b0;
        result_vl  = 1'b0;
        if (dec_buf_valid_q & (dec_committed_q | instr_commit_i)) begin
            if (dec_data_q.unit == UNIT_CFG) begin
                // vset[i]vl[i] instructions are not enqueued, return the result upon commit
                result_vl  = 1'b1;
            end else begin
                // attempt to enqueue all other instructions once they have been committed
                queue_push = 1'b1;
            end
        end
    end
    // return the result for instructions that do not write to an XREG as they are enqueued
    assign result_empty = queue_ready & queue_push & ((dec_data_q.unit != UNIT_ELEM) | ~dec_data_q.mode.elem.xreg);

    // decode buffer is vacated either by enqueueing an instruction, upon commit for vset[i]vl[i],
    // or when the instruction is killed; for vset[i]vl[i] it will take an additional cycle until
    // the CSR values are updated, hence the decode buffer is cleared without asserting dec_ready
    assign dec_ready = ~dec_buf_valid_q | (queue_ready & queue_push) | (dec_killed_q | instr_kill_i);
    assign dec_clear = result_vl;

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
        if (result_vl) begin
            vsew_d     = dec_data_q.mode.cfg.vsew;
            lmul_d     = dec_data_q.mode.cfg.lmul;
            agnostic_d = dec_data_q.mode.cfg.agnostic;
            if ((dec_data_q.mode.cfg.vsew == VSEW_INVALID) | ((dec_data_q.rs1.r.xval == 32'b0) & ~dec_data_q.mode.cfg.vlmax)) begin
                vl_0_d   = 1'b1;
                vl_d     = {CFG_VL_W{1'b0}};
                vl_csr_d = '0;
            end
            else if (dec_data_q.mode.cfg.keep_vl) begin
                // TODO keeping the current VL is only possible if the VSEW/LMUL ratio is not changed
            end else begin
                vl_0_d = 1'b0;
                vl_d   = DONT_CARE_ZERO ? '0 : 'x;
                unique case (dec_data_q.mode.cfg.lmul)
                    // TODO support fractional LMUL
                    LMUL_1: vl_d = ((cfg_avl[33:CFG_VL_W-3] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] : {3'b000, {(CFG_VL_W-3){1'b1}}};
                    LMUL_2: vl_d = ((cfg_avl[33:CFG_VL_W-2] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] : {2'b00,  {(CFG_VL_W-2){1'b1}}};
                    LMUL_4: vl_d = ((cfg_avl[33:CFG_VL_W-1] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] : {1'b0,   {(CFG_VL_W-1){1'b1}}};
                    LMUL_8: vl_d = ((cfg_avl[33:CFG_VL_W  ] == '0) & ~dec_data_q.mode.cfg.vlmax) ? cfg_avl[CFG_VL_W-1:0] :          { CFG_VL_W   {1'b1}} ;
                    default: ;
                endcase
                vl_csr_d = DONT_CARE_ZERO ? '0 : 'x;
                unique case ({dec_data_q.mode.cfg.lmul, dec_data_q.mode.cfg.vsew})
                    // TODO support fractional LMUL
                    {LMUL_1, VSEW_32}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-5] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {6'b1, {(CFG_VL_W-5){1'b0}}};
                    {LMUL_1, VSEW_16},
                    {LMUL_2, VSEW_32}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-4] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {5'b1, {(CFG_VL_W-4){1'b0}}};
                    {LMUL_1, VSEW_8 },
                    {LMUL_2, VSEW_16},
                    {LMUL_4, VSEW_32}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-3] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {4'b1, {(CFG_VL_W-3){1'b0}}};
                    {LMUL_2, VSEW_8 },
                    {LMUL_4, VSEW_16},
                    {LMUL_8, VSEW_32}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-2] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {3'b1, {(CFG_VL_W-2){1'b0}}};
                    {LMUL_4, VSEW_8 },
                    {LMUL_8, VSEW_16}: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W-1] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {2'b1, {(CFG_VL_W-1){1'b0}}};
                    {LMUL_8, VSEW_8 }: vl_csr_d = ((dec_data_q.rs1.r.xval[31:CFG_VL_W  ] == '0) & ~dec_data_q.mode.cfg.vlmax) ? dec_data_q.rs1.r.xval[CFG_VL_W:0] : {1'b1, {(CFG_VL_W  ){1'b0}}};
                    default: ;
                endcase
            end
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // INSTRUCTION QUEUE

    // acknowledge signal from the dispatcher (indicate that an instruction has
    // been accepted for execution on an execution unit)
    logic op_ack;

    // instruction queue output signals
    logic        queue_valid_q,     queue_valid_d;
    decoder_data queue_data_q,      queue_data_d;
    logic [31:0] queue_wr_hazard_q, queue_wr_hazard_d; // potential write hazards
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
                    queue_data_q      <= queue_data_d;
                    queue_wr_hazard_q <= queue_wr_hazard_d;
                end
            end
        end else begin
            assign queue_valid_q     = queue_valid_d;
            assign queue_data_q      = queue_data_d;
            assign queue_wr_hazard_q = queue_wr_hazard_d;
        end
    endgenerate

    // instruction queue
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
                .deq_data_o   ( queue_data_d            )
            );
        end else begin
            assign queue_valid_d = queue_push;
            assign queue_ready   = ~queue_valid_q | op_ack;
            assign queue_data_d  = dec_data_q;
        end
    endgenerate

    // potential vector register hazards of the currently dequeued instruction
    vproc_hazards #(
        .DONT_CARE_ZERO ( DONT_CARE_ZERO          )
    ) queue_hazards (
        .vsew_i         ( queue_data_d.vsew       ),
        .lmul_i         ( queue_data_d.lmul       ),
        .unit_i         ( queue_data_d.unit       ),
        .mode_i         ( queue_data_d.mode       ),
        .widenarrow_i   ( queue_data_d.widenarrow ),
        .rs1_i          ( queue_data_d.rs1        ),
        .rs2_i          ( queue_data_d.rs2        ),
        .rd_i           ( queue_data_d.rd         ),
        .rd_hazards_o   (                         ),
        .wr_hazards_o   ( queue_wr_hazard_d       )
    );

    // keep track of pending loads and stores
    logic pending_load_lsu, pending_store_lsu;
    assign pending_load_o  = (dec_buf_valid_q & (dec_data_q.unit   == UNIT_LSU) & ~dec_data_q.mode.lsu.store  ) |
                             (queue_valid_q   & (queue_data_q.unit == UNIT_LSU) & ~queue_data_q.mode.lsu.store) |
                             pending_load_lsu;
    assign pending_store_o = (dec_buf_valid_q & (dec_data_q.unit   == UNIT_LSU) &  dec_data_q.mode.lsu.store  ) |
                             (queue_valid_q   & (queue_data_q.unit == UNIT_LSU) &  queue_data_q.mode.lsu.store) |
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
    assign pending_hazards = (queue_wr_hazard_q & vreg_wr_hazard_map_q) != 32'b0;

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
                // regular operations are only performed when the current
                // configuration is valid
                UNIT_LSU:  op_rdy_lsu  = queue_data_q.vsew != VSEW_INVALID;
                UNIT_ALU:  op_rdy_alu  = queue_data_q.vsew != VSEW_INVALID;
                UNIT_MUL:  op_rdy_mul  = queue_data_q.vsew != VSEW_INVALID;
                UNIT_SLD:  op_rdy_sld  = queue_data_q.vsew != VSEW_INVALID;
                UNIT_ELEM: op_rdy_elem = queue_data_q.vsew != VSEW_INVALID;
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
            vreg_wr_hazard_map_set = queue_wr_hazard_q;
        end
    end

    // vreg hazard clearing:
    logic [31:0] vreg_rd_hazard_clr_lsu,  vreg_wr_hazard_clr_lsu;
    logic [31:0] vreg_rd_hazard_clr_alu,  vreg_wr_hazard_clr_alu;
    logic [31:0] vreg_rd_hazard_clr_mul,  vreg_wr_hazard_clr_mul;
    logic [31:0] vreg_rd_hazard_clr_sld,  vreg_wr_hazard_clr_sld;
    logic [31:0] vreg_rd_hazard_clr_elem, vreg_wr_hazard_clr_elem;
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
    logic              misaligned_lsu;
    logic [VREG_W-1:0] lsu_wr_data;
    logic [VMSK_W-1:0] lsu_wr_mask;
    logic [4:0]        lsu_wr_addr;
    logic              lsu_wr_en;
    vproc_lsu #(
        .VREG_W             ( VREG_W                        ),
        .VMSK_W             ( VMSK_W                        ),
        .VMEM_W             ( VMEM_W                        ),
        .CFG_VL_W           ( CFG_VL_W                      ),
        .MAX_WR_ATTEMPTS    ( 1                             ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO                )
    ) lsu (
        .clk_i              ( clk_i                         ),
        .async_rst_ni       ( async_rst_n                   ),
        .sync_rst_ni        ( sync_rst_n                    ),
        .vsew_i             ( queue_data_q.vsew             ),
        .lmul_i             ( queue_data_q.lmul             ),
        .vl_i               ( queue_data_q.vl               ),
        .vl_0_i             ( queue_data_q.vl_0             ),
        .op_rdy_i           ( op_rdy_lsu                    ),
        .op_ack_o           ( op_ack_lsu                    ),
        .misaligned_o       ( misaligned_lsu                ),
        .mode_i             ( queue_data_q.mode.lsu         ),
        .rs1_val_i          ( queue_data_q.rs1.r.xval       ),
        .rs2_i              ( queue_data_q.rs2              ),
        .vd_i               ( queue_data_q.rd.addr          ),
        .vreg_pend_wr_i     ( vreg_wr_hazard_map_q          ),
        .vreg_pend_rd_o     ( vreg_pend_rd_by_lsu_d         ),
        .vreg_pend_rd_i     ( vreg_pend_rd_to_lsu_q         ),
        .pending_load_o     ( pending_load_lsu              ),
        .pending_store_o    ( pending_store_lsu             ),
        .clear_rd_hazards_o ( vreg_rd_hazard_clr_lsu        ),
        .clear_wr_hazards_o ( vreg_wr_hazard_clr_lsu        ),
        .vreg_mask_i        ( vreg_mask                     ),
        .vreg_rd_i          ( vregfile_rd_data[1]           ),
        .vreg_rd_addr_o     ( vregfile_rd_addr[1]           ),
        .vreg_wr_o          ( lsu_wr_data                   ),
        .vreg_wr_addr_o     ( lsu_wr_addr                   ),
        .vreg_wr_mask_o     ( lsu_wr_mask                   ),
        .vreg_wr_en_o       ( lsu_wr_en                     ),
        .data_gnt_i         ( data_gnt_i                    ),
        .data_rvalid_i      ( data_rvalid_i                 ),
        .data_err_i         ( data_err_i                    ),
        .data_rdata_i       ( data_rdata_i                  ),
        .data_req_o         ( data_req_o                    ),
        .data_addr_o        ( data_addr_o                   ),
        .data_we_o          ( data_we_o                     ),
        .data_be_o          ( data_be_o                     ),
        .data_wdata_o       ( data_wdata_o                  )
    );
    assign misaligned_ls_o = misaligned_lsu & op_ack_lsu;


    // ALU
    logic [VREG_W-1:0] alu_wr_data;
    logic [VMSK_W-1:0] alu_wr_mask;
    logic [4:0]        alu_wr_addr;
    logic              alu_wr_en;
    vproc_alu #(
        .VREG_W             ( VREG_W                        ),
        .VMSK_W             ( VMSK_W                        ),
        .CFG_VL_W           ( CFG_VL_W                      ),
        .ALU_OP_W           ( ALU_OP_W                      ),
        .MAX_WR_ATTEMPTS    ( 2                             ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO                )
    ) alu (
        .clk_i              ( clk_i                         ),
        .async_rst_ni       ( async_rst_n                   ),
        .sync_rst_ni        ( sync_rst_n                    ),
        .vsew_i             ( queue_data_q.vsew             ),
        .lmul_i             ( queue_data_q.lmul             ),
        .vl_i               ( queue_data_q.vl               ),
        .vl_0_i             ( queue_data_q.vl_0             ),
        .op_rdy_i           ( op_rdy_alu                    ),
        .op_ack_o           ( op_ack_alu                    ),
        .mode_i             ( queue_data_q.mode.alu         ),
        .widenarrow_i       ( queue_data_q.widenarrow       ),
        .rs1_i              ( queue_data_q.rs1              ),
        .vs2_i              ( queue_data_q.rs2.r.vaddr      ),
        .vs2_vreg_i         ( queue_data_q.rs2.vreg         ),
        .vd_i               ( queue_data_q.rd.addr          ),
        .vreg_pend_wr_i     ( vreg_wr_hazard_map_q          ),
        .vreg_pend_rd_o     ( vreg_pend_rd_by_alu_d         ),
        .vreg_pend_rd_i     ( vreg_pend_rd_to_alu_q         ),
        .clear_rd_hazards_o ( vreg_rd_hazard_clr_alu        ),
        .clear_wr_hazards_o ( vreg_wr_hazard_clr_alu        ),
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
        .MAX_WR_ATTEMPTS    ( 1                                      ),
        .MUL_TYPE           ( MUL_TYPE                               ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO                         )
    ) mul (
        .clk_i              ( clk_i                                  ),
        .async_rst_ni       ( async_rst_n                            ),
        .sync_rst_ni        ( sync_rst_n                             ),
        .vsew_i             ( queue_data_q.vsew                      ),
        .lmul_i             ( queue_data_q.lmul                      ),
        .vl_i               ( queue_data_q.vl                        ),
        .vl_0_i             ( queue_data_q.vl_0                      ),
        .op_rdy_i           ( op_rdy_mul                             ),
        .op_ack_o           ( op_ack_mul                             ),
        .mode_i             ( queue_data_q.mode.mul                  ),
        .widening_i         ( queue_data_q.widenarrow == OP_WIDENING ),
        .rs1_i              ( queue_data_q.rs1                       ),
        .vs2_i              ( queue_data_q.rs2.r.vaddr               ),
        .vd_i               ( queue_data_q.rd.addr                   ),
        .vreg_pend_wr_i     ( vreg_wr_hazard_map_q                   ),
        .vreg_pend_rd_o     ( vreg_pend_rd_by_mul_d                  ),
        .vreg_pend_rd_i     ( vreg_pend_rd_to_mul_q                  ),
        .clear_rd_hazards_o ( vreg_rd_hazard_clr_mul                 ),
        .clear_wr_hazards_o ( vreg_wr_hazard_clr_mul                 ),
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
        .MAX_WR_ATTEMPTS    ( 2                        ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO           )
    ) sld (
        .clk_i              ( clk_i                    ),
        .async_rst_ni       ( async_rst_n              ),
        .sync_rst_ni        ( sync_rst_n               ),
        .vsew_i             ( queue_data_q.vsew        ),
        .lmul_i             ( queue_data_q.lmul        ),
        .vl_i               ( queue_data_q.vl          ),
        .vl_0_i             ( queue_data_q.vl_0        ),
        .op_rdy_i           ( op_rdy_sld               ),
        .op_ack_o           ( op_ack_sld               ),
        .mode_i             ( queue_data_q.mode.sld    ),
        .rs1_i              ( queue_data_q.rs1.r.xval  ),
        .vs2_i              ( queue_data_q.rs2.r.vaddr ),
        .vd_i               ( queue_data_q.rd.addr     ),
        .vreg_pend_wr_i     ( vreg_wr_hazard_map_q     ),
        .vreg_pend_rd_o     ( vreg_pend_rd_by_sld_d    ),
        .vreg_pend_rd_i     ( vreg_pend_rd_to_sld_q    ),
        .clear_rd_hazards_o ( vreg_rd_hazard_clr_sld   ),
        .clear_wr_hazards_o ( vreg_wr_hazard_clr_sld   ),
        .vreg_mask_i        ( vreg_mask                ),
        .vreg_rd_i          ( vregfile_rd_data[5]      ),
        .vreg_rd_addr_o     ( vregfile_rd_addr[5]      ),
        .vreg_wr_o          ( sld_wr_data              ),
        .vreg_wr_addr_o     ( sld_wr_addr              ),
        .vreg_wr_mask_o     ( sld_wr_mask              ),
        .vreg_wr_en_o       ( sld_wr_en                )
    );


    // ELEM unit
    logic [VREG_W-1:0] elem_wr_data;
    logic [VMSK_W-1:0] elem_wr_mask;
    logic [4:0]        elem_wr_addr;
    logic              elem_wr_en;
    logic              elem_xreg_valid;
    logic [31:0]       elem_xreg;
    vproc_elem #(
        .VREG_W             ( VREG_W                   ),
        .VMSK_W             ( VMSK_W                   ),
        .CFG_VL_W           ( CFG_VL_W                 ),
        .GATHER_OP_W        ( GATHER_OP_W              ),
        .MAX_WR_ATTEMPTS    ( 3                        ),
        .DONT_CARE_ZERO     ( DONT_CARE_ZERO           )
    ) elem (
        .clk_i              ( clk_i                    ),
        .async_rst_ni       ( async_rst_n              ),
        .sync_rst_ni        ( sync_rst_n               ),
        .vsew_i             ( queue_data_q.vsew        ),
        .lmul_i             ( queue_data_q.lmul        ),
        .vl_i               ( queue_data_q.vl          ),
        .vl_0_i             ( queue_data_q.vl_0        ),
        .op_rdy_i           ( op_rdy_elem              ),
        .op_ack_o           ( op_ack_elem              ),
        .mode_i             ( queue_data_q.mode.elem   ),
        .vs1_i              ( queue_data_q.rs1.r.vaddr ),
        .vs1_vreg_i         ( queue_data_q.rs1.vreg    ),
        .vs2_i              ( queue_data_q.rs2.r.vaddr ),
        .vs2_vreg_i         ( queue_data_q.rs2.vreg    ),
        .vd_i               ( queue_data_q.rd.addr     ),
        .vreg_pend_wr_i     ( vreg_wr_hazard_map_q     ),
        .vreg_pend_rd_o     ( vreg_pend_rd_by_elem_d   ),
        .vreg_pend_rd_i     ( vreg_pend_rd_to_elem_q   ),
        .clear_rd_hazards_o ( vreg_rd_hazard_clr_elem  ),
        .clear_wr_hazards_o ( vreg_wr_hazard_clr_elem  ),
        .vreg_mask_i        ( vreg_mask                ),
        .vreg_rd_i          ( vregfile_rd_data[6]      ),
        .vreg_rd_addr_o     ( vregfile_rd_addr[6]      ),
        .vreg_wr_o          ( elem_wr_data             ),
        .vreg_wr_addr_o     ( elem_wr_addr             ),
        .vreg_wr_mask_o     ( elem_wr_mask             ),
        .vreg_wr_en_o       ( elem_wr_en               ),
        .xreg_valid_o       ( elem_xreg_valid          ),
        .xreg_o             ( elem_xreg                )
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

    // TODO: take care of simultaneous results from commit stage and ELEM unit

    logic        result_valid_q, result_valid_d;
    logic        result_vl_q,    result_vl_d;
    logic        result_xreg_q,  result_xreg_d;
    logic [31:0] result_data_q,  result_data_d;
    always_ff @(posedge clk_i or negedge async_rst_n) begin : vproc_result_valid
        if (~async_rst_n) begin
            result_valid_q <= 1'b0;
        end
        else if (~sync_rst_n) begin
            result_valid_q <= 1'b0;
        end
        else begin
            result_valid_q <= result_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin : vproc_result
        result_vl_q   <= result_vl_d;
        result_xreg_q <= result_xreg_d;
        result_data_q <= result_data_d;
    end
    always_comb begin
        result_valid_d = result_valid_q;
        result_vl_d    = result_vl_q;
        result_xreg_d  = result_xreg_q;
        result_data_d  = result_data_q;
        if (~result_valid_q | result_ready_i) begin
            result_valid_d = result_empty | result_vl | elem_xreg_valid;
            result_vl_d    = result_vl;
            result_xreg_d  = elem_xreg_valid;
            result_data_d  = elem_xreg;
        end
    end
    assign result_valid_o = result_valid_q;
    assign xreg_valid_o   = result_vl_q | result_xreg_q;
    assign xreg_o         = result_vl_q ? csr_vl_o : result_data_q;

endmodule
