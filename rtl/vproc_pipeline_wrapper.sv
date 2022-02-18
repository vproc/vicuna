// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_pipeline_wrapper #(
        parameter int unsigned          VREG_W           = 128,  // width in bits of vector registers
        parameter int unsigned          CFG_VL_W         = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned          XIF_ID_W         = 3,    // width in bits of instruction IDs
        parameter int unsigned          XIF_ID_CNT       = 8,    // total count of instruction IDs
        parameter vproc_pkg::op_unit    UNIT             = UNIT_ALU,
        parameter int unsigned          MAX_OP_W         = 64,   // operand width in bits
        parameter vproc_pkg::mul_type   MUL_TYPE         = vproc_pkg::MUL_GENERIC,
        parameter int unsigned          MAX_WR_ATTEMPTS  = 1,    // max required vregfile write attempts
        parameter bit                   DONT_CARE_ZERO   = 1'b0  // initialize don't care values to zero
    )(
        input  logic                    clk_i,
        input  logic                    async_rst_ni,
        input  logic                    sync_rst_ni,

        input  logic [XIF_ID_W-1:0]     id_i,
        input  vproc_pkg::cfg_vsew      vsew_i,
        input  vproc_pkg::cfg_emul      emul_i,
        input  vproc_pkg::cfg_vxrm      vxrm_i,
        input  logic [CFG_VL_W-1:0]     vl_i,
        input  logic                    vl_0_i,

        input  logic                    op_rdy_i,
        output logic                    op_ack_o,

        input  vproc_pkg::op_mode       mode_i,
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

        input  logic [VREG_W-1:0]       vreg_mask_i,
        input  logic [VREG_W-1:0]       vreg_rd_i,
        output logic [4:0]              vreg_rd_addr_o,
        input  logic [VREG_W-1:0]       vreg_rd3_i,
        output logic [4:0]              vreg_rd3_addr_o,
        output logic [VREG_W-1:0]       vreg_wr_o,
        output logic [4:0]              vreg_wr_addr_o,
        output logic [VREG_W/8-1:0]     vreg_wr_mask_o,
        output logic                    vreg_wr_en_o,

        output logic                    pending_load_o,
        output logic                    pending_store_o,

        vproc_xif.coproc_mem            xif_mem_if,
        vproc_xif.coproc_mem_result     xif_memres_if,

        output logic                    trans_complete_valid_o,
        output logic [XIF_ID_W-1:0]     trans_complete_id_o,
        output logic                    trans_complete_exc_o,
        output logic [5:0]              trans_complete_exccode_o,

        output logic                    xreg_valid_o,
        output logic [XIF_ID_W-1:0]     xreg_id_o,
        output logic [4:0]              xreg_addr_o,
        output logic [31:0]             xreg_data_o
    );

    import vproc_pkg::*;

    localparam int unsigned VPORT_CNT  =  (UNIT == UNIT_MUL)                        ? 3 : 2;

    localparam int unsigned OP_CNT     = ((UNIT == UNIT_MUL) | (UNIT == UNIT_ELEM)) ? 4 : (
                                          (UNIT == UNIT_SLD)                        ? 2 : 3);

    // operand widths
    localparam int unsigned DFLT_OP_W  = (UNIT == UNIT_ELEM) ? 32 : MAX_OP_W;    // default width
    localparam int unsigned FIRST_OP_W = (UNIT == UNIT_LSU ) ? 32 : DFLT_OP_W;   // first operand
    localparam int unsigned EXTRA_OP_W = MAX_OP_W;                               // extra operand
    localparam int unsigned MASK_OP_W  = (UNIT == UNIT_ELEM) ? 1  : DFLT_OP_W/8; // v0 mask width

    // number of stages for operand unpacking
    localparam int unsigned UNPACK_STAGES = (UNIT == UNIT_SLD) ? 2 : ((UNIT == UNIT_ELEM) ? 4 : 3);

    // result count and default width
    localparam int unsigned RES_CNT   = (UNIT == UNIT_ALU ) ? 2  : 1;
    localparam int unsigned MAX_RES_W = (UNIT == UNIT_ELEM) ? 32 : MAX_OP_W;

    generate
        if (VPORT_CNT == 2 && OP_CNT == 2 && RES_CNT == 1) begin
            localparam int unsigned VPORT_W [2] = '{VREG_W, VREG_W};
            localparam int unsigned VADDR_W [2] = '{5, 5};

            localparam int unsigned OP_W    [2] = '{FIRST_OP_W, MASK_OP_W};
            localparam int unsigned OP_STAGE[2] = '{1, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC  [2] = '{0, VPORT_CNT-1};

            localparam int unsigned RES_W   [1] = '{MAX_RES_W};

            vproc_pipeline #(
                .VREG_W          ( VREG_W          ),
                .CFG_VL_W        ( CFG_VL_W        ),
                .XIF_ID_W        ( XIF_ID_W        ),
                .XIF_ID_CNT      ( XIF_ID_CNT      ),
                .UNIT            ( UNIT            ),
                .VPORT_CNT       ( VPORT_CNT       ),
                .VPORT_W         ( VPORT_W         ),
                .VADDR_W         ( VADDR_W         ),
                .MAX_OP_W        ( MAX_OP_W        ),
                .OP_CNT          ( OP_CNT          ),
                .OP_W            ( OP_W            ),
                .OP_STAGE        ( OP_STAGE        ),
                .OP_SRC          ( OP_SRC          ),
                .UNPACK_STAGES   ( UNPACK_STAGES   ),
                .MAX_RES_W       ( MAX_RES_W       ),
                .RES_CNT         ( RES_CNT         ),
                .RES_W           ( RES_W           ),
                .MUL_TYPE        ( MUL_TYPE        ),
                .MAX_WR_ATTEMPTS ( MAX_WR_ATTEMPTS ),
                .DONT_CARE_ZERO  ( DONT_CARE_ZERO  )
            ) pipeline (
                .*
            );
        end
        else if (VPORT_CNT == 2 && OP_CNT == 3 && RES_CNT == 1) begin
            localparam int unsigned VPORT_W [2] = '{VREG_W, VREG_W};
            localparam int unsigned VADDR_W [2] = '{5, 5};

            localparam int unsigned OP_W    [3] = '{FIRST_OP_W, DFLT_OP_W, MASK_OP_W};
            localparam int unsigned OP_STAGE[3] = '{1, 2, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC  [3] = '{0, 0, VPORT_CNT-1};

            localparam int unsigned RES_W   [1] = '{MAX_RES_W};

            vproc_pipeline #(
                .VREG_W          ( VREG_W          ),
                .CFG_VL_W        ( CFG_VL_W        ),
                .XIF_ID_W        ( XIF_ID_W        ),
                .XIF_ID_CNT      ( XIF_ID_CNT      ),
                .UNIT            ( UNIT            ),
                .VPORT_CNT       ( VPORT_CNT       ),
                .VPORT_W         ( VPORT_W         ),
                .VADDR_W         ( VADDR_W         ),
                .MAX_OP_W        ( MAX_OP_W        ),
                .OP_CNT          ( OP_CNT          ),
                .OP_W            ( OP_W            ),
                .OP_STAGE        ( OP_STAGE        ),
                .OP_SRC          ( OP_SRC          ),
                .UNPACK_STAGES   ( UNPACK_STAGES   ),
                .MAX_RES_W       ( MAX_RES_W       ),
                .RES_CNT         ( RES_CNT         ),
                .RES_W           ( RES_W           ),
                .MUL_TYPE        ( MUL_TYPE        ),
                .MAX_WR_ATTEMPTS ( MAX_WR_ATTEMPTS ),
                .DONT_CARE_ZERO  ( DONT_CARE_ZERO  )
            ) pipeline (
                .*
            );
        end
        else if (VPORT_CNT == 2 && OP_CNT == 3 && RES_CNT == 2) begin
            localparam int unsigned VPORT_W [2] = '{VREG_W, VREG_W};
            localparam int unsigned VADDR_W [2] = '{5, 5};

            localparam int unsigned OP_W    [3] = '{FIRST_OP_W, DFLT_OP_W, MASK_OP_W};
            localparam int unsigned OP_STAGE[3] = '{1, 2, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC  [3] = '{0, 0, VPORT_CNT-1};

            localparam int unsigned RES_W   [2] = '{MAX_RES_W, MAX_RES_W/8};

            vproc_pipeline #(
                .VREG_W          ( VREG_W          ),
                .CFG_VL_W        ( CFG_VL_W        ),
                .XIF_ID_W        ( XIF_ID_W        ),
                .XIF_ID_CNT      ( XIF_ID_CNT      ),
                .UNIT            ( UNIT            ),
                .VPORT_CNT       ( VPORT_CNT       ),
                .VPORT_W         ( VPORT_W         ),
                .VADDR_W         ( VADDR_W         ),
                .MAX_OP_W        ( MAX_OP_W        ),
                .OP_CNT          ( OP_CNT          ),
                .OP_W            ( OP_W            ),
                .OP_STAGE        ( OP_STAGE        ),
                .OP_SRC          ( OP_SRC          ),
                .UNPACK_STAGES   ( UNPACK_STAGES   ),
                .MAX_RES_W       ( MAX_RES_W       ),
                .RES_CNT         ( RES_CNT         ),
                .RES_W           ( RES_W           ),
                .MUL_TYPE        ( MUL_TYPE        ),
                .MAX_WR_ATTEMPTS ( MAX_WR_ATTEMPTS ),
                .DONT_CARE_ZERO  ( DONT_CARE_ZERO  )
            ) pipeline (
                .*
            );
        end
        else if (VPORT_CNT == 2 && OP_CNT == 4 && RES_CNT == 1) begin
            localparam int unsigned VPORT_W [2] = '{VREG_W, VREG_W};
            localparam int unsigned VADDR_W [2] = '{5, 5};

            localparam int unsigned OP_W    [4] = '{FIRST_OP_W, DFLT_OP_W, EXTRA_OP_W, MASK_OP_W};
            localparam int unsigned OP_STAGE[4] = '{1, 2, UNPACK_STAGES-1, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC  [4] = '{0, 0, VPORT_CNT-2, VPORT_CNT-1};

            localparam int unsigned RES_W   [1] = '{MAX_RES_W};

            vproc_pipeline #(
                .VREG_W          ( VREG_W          ),
                .CFG_VL_W        ( CFG_VL_W        ),
                .XIF_ID_W        ( XIF_ID_W        ),
                .XIF_ID_CNT      ( XIF_ID_CNT      ),
                .UNIT            ( UNIT            ),
                .VPORT_CNT       ( VPORT_CNT       ),
                .VPORT_W         ( VPORT_W         ),
                .VADDR_W         ( VADDR_W         ),
                .MAX_OP_W        ( MAX_OP_W        ),
                .OP_CNT          ( OP_CNT          ),
                .OP_W            ( OP_W            ),
                .OP_STAGE        ( OP_STAGE        ),
                .OP_SRC          ( OP_SRC          ),
                .UNPACK_STAGES   ( UNPACK_STAGES   ),
                .MAX_RES_W       ( MAX_RES_W       ),
                .RES_CNT         ( RES_CNT         ),
                .RES_W           ( RES_W           ),
                .MUL_TYPE        ( MUL_TYPE        ),
                .MAX_WR_ATTEMPTS ( MAX_WR_ATTEMPTS ),
                .DONT_CARE_ZERO  ( DONT_CARE_ZERO  )
            ) pipeline (
                .*
            );
        end
        else if (VPORT_CNT == 3 && OP_CNT == 4 && RES_CNT == 1) begin
            localparam int unsigned VPORT_W [3] = '{VREG_W, VREG_W, VREG_W};
            localparam int unsigned VADDR_W [3] = '{5, 5, 5};

            localparam int unsigned OP_W    [4] = '{FIRST_OP_W, DFLT_OP_W, EXTRA_OP_W, MASK_OP_W};
            localparam int unsigned OP_STAGE[4] = '{1, 2, UNPACK_STAGES-1, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC  [4] = '{0, 0, VPORT_CNT-2, VPORT_CNT-1};

            localparam int unsigned RES_W   [1] = '{MAX_RES_W};

            vproc_pipeline #(
                .VREG_W          ( VREG_W          ),
                .CFG_VL_W        ( CFG_VL_W        ),
                .XIF_ID_W        ( XIF_ID_W        ),
                .XIF_ID_CNT      ( XIF_ID_CNT      ),
                .UNIT            ( UNIT            ),
                .VPORT_CNT       ( VPORT_CNT       ),
                .VPORT_W         ( VPORT_W         ),
                .VADDR_W         ( VADDR_W         ),
                .MAX_OP_W        ( MAX_OP_W        ),
                .OP_CNT          ( OP_CNT          ),
                .OP_W            ( OP_W            ),
                .OP_STAGE        ( OP_STAGE        ),
                .OP_SRC          ( OP_SRC          ),
                .UNPACK_STAGES   ( UNPACK_STAGES   ),
                .MAX_RES_W       ( MAX_RES_W       ),
                .RES_CNT         ( RES_CNT         ),
                .RES_W           ( RES_W           ),
                .MUL_TYPE        ( MUL_TYPE        ),
                .MAX_WR_ATTEMPTS ( MAX_WR_ATTEMPTS ),
                .DONT_CARE_ZERO  ( DONT_CARE_ZERO  )
            ) pipeline (
                .*
            );
        end
    endgenerate

endmodule
