// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_pipeline_wrapper #(
        parameter int unsigned          VREG_W             = 128,  // width in bits of vector registers
        parameter int unsigned          CFG_VL_W           = 7,    // width of VL reg in bits (= log2(VREG_W))
        parameter int unsigned          XIF_ID_W           = 3,    // width in bits of instruction IDs
        parameter int unsigned          XIF_ID_CNT         = 8,    // total count of instruction IDs
        parameter bit [vproc_pkg::UNIT_CNT-1:0] UNITS      = '0,
        parameter int unsigned          MAX_VPORT_W        = 128,  // max port width
        parameter int unsigned          MAX_VADDR_W        = 5,    // max addr width
        parameter int unsigned          VPORT_CNT          = 1,
`ifdef VERILATOR
        // Workaround for Verilator due to https://github.com/verilator/verilator/issues/3433
        parameter int unsigned          VPORT_OFFSET       = 0,
        parameter int unsigned          VREGFILE_VPORT_CNT = 1,
        parameter int unsigned          VREGFILE_VPORT_W[VREGFILE_VPORT_CNT] = '{0},
        parameter int unsigned          VREGFILE_VADDR_W[VREGFILE_VPORT_CNT] = '{0},
`else
        parameter int unsigned          VPORT_W[VPORT_CNT] = '{0},
        parameter int unsigned          VADDR_W[VPORT_CNT] = '{0},
`endif
        parameter bit [VPORT_CNT-1:0]   VPORT_BUFFER       = '0,   // buffer port
        parameter bit                   VPORT_V0           = '0,   // use dedicated v0 read port
        parameter int unsigned          MAX_OP_W           = 64,   // operand width in bits
        parameter vproc_pkg::mul_type   MUL_TYPE           = vproc_pkg::MUL_GENERIC,
        parameter bit                   ADDR_ALIGNED       = 1'b1, // base address is aligned to VMEM_W
        parameter int unsigned          MAX_WR_ATTEMPTS    = 1,    // max required vregfile write attempts
        parameter type                  DECODER_DATA_T     = logic,
        parameter bit                   DONT_CARE_ZERO     = 1'b0  // initialize don't care values to zero
    )(
        input  logic                    clk_i,
        input  logic                    async_rst_ni,
        input  logic                    sync_rst_ni,

        input  logic                    pipe_in_valid_i,
        output logic                    pipe_in_ready_o,
        input  DECODER_DATA_T           pipe_in_data_i,

        input  logic [31:0]             vreg_pend_wr_i,
        output logic [31:0]             vreg_pend_rd_o,
        input  logic [31:0]             vreg_pend_rd_i,

        output logic [31:0]             clear_wr_hazards_o,

        input  logic [XIF_ID_CNT-1:0]   instr_spec_i,
        input  logic [XIF_ID_CNT-1:0]   instr_killed_i,
        output logic                    instr_done_valid_o,
        output logic [XIF_ID_W-1:0]     instr_done_id_o,

        output logic [VPORT_CNT-1:0][MAX_VADDR_W-1:0] vreg_rd_addr_o,       // vreg read address
        input  logic [VPORT_CNT-1:0][MAX_VPORT_W-1:0] vreg_rd_data_i,       // vreg read data
        input  logic                [VREG_W     -1:0] vreg_rd_v0_i,         // vreg v0 read data

        output logic                    vreg_wr_valid_o,
        input  logic                    vreg_wr_ready_i,
        output logic [4:0]              vreg_wr_addr_o,
        output logic [VREG_W/8-1:0]     vreg_wr_be_o,
        output logic [VREG_W  -1:0]     vreg_wr_data_o,

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

`ifdef VERILATOR
    // Workaround for Verilator due to https://github.com/verilator/verilator/issues/3433
    typedef int unsigned VERILATOR_ARRAY_SLICE_T[VPORT_CNT];
    function static VERILATOR_ARRAY_SLICE_T VERILATOR_ARRAY_SLICE(int unsigned SRC[VPORT_CNT]);
        for (int i = 0; i < VPORT_CNT; i++) begin
            VERILATOR_ARRAY_SLICE[i] = SRC[VPORT_OFFSET + i];
        end
    endfunction
    localparam int unsigned VPORT_W[VPORT_CNT] = VERILATOR_ARRAY_SLICE(VREGFILE_VPORT_W);
    localparam int unsigned VADDR_W[VPORT_CNT] = VERILATOR_ARRAY_SLICE(VREGFILE_VADDR_W);
`endif

    import vproc_pkg::*;

    // OPERAND DEFINITIONS
    // The operand count depends on the units used within a pipeline.  Most units require two
    // regular operands and a mask.  The SLD unit requires only one regular operand and a mask.
    // The MUL requires a regular third operand and the ELEM unit requires an operand addressed
    // by indices loaded by a previous operand.  These operands have following indices (negative
    // indices must be added to the operand count):
    //
    //  | Idx | Type | Address  | Units using it | Comment                                       |
    //  +-----+------+----------+----------------+-----------------------------------------------+
    //  |  0  | data | vs2 (vd) |      all       | Only MUL may change address to vd             |
    //  |  1  | data | vs1 (vd) | all except SLD | Only LSU uses vd as address instead of vs1    |
    //  |  2  | data |  vd/vs2  |      MUL       | MUL may use either vd or vs2 as address       |
    //  | -3  | data | dynamic  |     ELEM       | Index-based dynamic address within vreg group |
    //  | -2  | mask |   vs2    |     ELEM       | Mask operand for some ELEM operations         |
    //  | -1  | mask |    v0    |      all       | Mask operand for masked operations            |

    // Operand count:
    // - default is 3 (indices 0, 1, and -1 from above table, required by almost all units)
    // - MUL unit additionally requires index 2, raising the operand count to a minimum of 4
    // - ELEM unit additionally requires indices -3 and -2, hence a minimum of 5 operands
    // - if MUL and ELEM units are both present in same pipeline, then all 6 operands are required
    // - in case a pipeline contains only the SLD unit the operand count is 2 (indices 0 and -1)
    localparam int unsigned OP_CNT        = UNITS[UNIT_MUL] ? (
                                                UNITS[UNIT_ELEM] ? 6 : 4
                                            ) : (
                                                UNITS[UNIT_ELEM] ? 5 : (
                                                    (UNITS == (UNIT_CNT'(1) << UNIT_SLD)) ? 2 : 3
                                                )
                                            );

    // Number of stages for operand unpacking
    localparam int unsigned UNPACK_STAGES = UNITS[UNIT_ELEM] ? 4 : (
                                                (UNITS == (UNIT_CNT'(1) << UNIT_SLD)) ? 2 : 3
                                            );

    // operand flags
    localparam bit OP_DYN_ADDR_OFFSET     = UNITS[UNIT_ELEM];   // operand with dynamic addr used
    localparam bit OP_SECOND_MASK         = UNITS[UNIT_ELEM];   // second mask operand used
    localparam bit OP0_NARROW             = UNITS[UNIT_MUL] | UNITS[UNIT_ALU] | UNITS[UNIT_ELEM];
    localparam bit OP1_NARROW             = UNITS[UNIT_MUL] | UNITS[UNIT_ALU];
    localparam bit OP1_XREG               = UNITS[UNIT_MUL] | UNITS[UNIT_ALU];
    localparam bit OP0_ELEMWISE           = UNITS[UNIT_LSU] | UNITS[UNIT_ELEM];
    localparam bit OP1_ELEMWISE           = UNITS[UNIT_LSU] | UNITS[UNIT_ELEM];
    localparam bit OPMASK_ELEMWISE        = UNITS[UNIT_LSU] | UNITS[UNIT_ELEM];
    localparam bit OP0_ALT_COUNTER        = UNITS[UNIT_SLD];

    // result count and default width
    localparam int unsigned RES_CNT       = UNITS[UNIT_ALU] ? 2 : 1;
    localparam int unsigned MAX_RES_W     = MAX_OP_W;

    // result flags
    localparam bit RES0_ALWAYS_VREG       = ~UNITS[UNIT_LSU] & ~UNITS[UNIT_ALU] & ~UNITS[UNIT_ELEM];
    localparam bit RES0_NARROW            = UNITS[UNIT_ALU];
    localparam bit RES0_ALLOW_ELEMWISE    = UNITS[UNIT_LSU] | UNITS[UNIT_ELEM];

    // other pipeline flags
    localparam bit MAY_FLUSH              = UNITS[UNIT_ELEM];   // the pipeline may require flushing


    ///////////////////////////////////////////////////////////////////////////
    // CONVERT DECODER DATA TO INITIAL PIPELINE STATE

    localparam int unsigned ALT_COUNT_W = $clog2(VREG_W/MAX_OP_W) + 4;

    typedef struct packed {
        logic                            count_extra_phase; // start by counting an extra phase
        logic        [ALT_COUNT_W  -1:0] alt_count_init;    // alternative counter init value
        count_inc_e                      count_inc;         // counter increment policy
        logic                            requires_flush;    // whether the instr requires flushing
        logic        [XIF_ID_W     -1:0] id;
        op_unit                          unit;
        op_mode                          mode;
        cfg_vsew                         eew;               // effective element width
        cfg_emul                         emul;              // effective MUL factor
        cfg_vxrm                         vxrm;
        logic        [CFG_VL_W     -1:0] vl;
        logic                            vl_0;
        logic                     [31:0] xval;
        unpack_flags [OP_CNT -1:0]       op_flags;
        logic        [OP_CNT -1:0][4 :0] op_vaddr;
        logic        [OP_CNT -1:0][31:0] op_xval;
        logic        [RES_CNT-1:0]       res_vreg;
        logic        [RES_CNT-1:0]       res_narrow;
        logic                     [4 :0] res_vaddr;
    } state_t;

    // identify the unit of the supplied instruction
    logic unit_lsu, unit_alu, unit_mul, unit_sld, unit_elem;
    assign unit_lsu  = UNITS[UNIT_LSU ] & (pipe_in_data_i.unit == UNIT_LSU );
    assign unit_alu  = UNITS[UNIT_ALU ] & (pipe_in_data_i.unit == UNIT_ALU );
    assign unit_mul  = UNITS[UNIT_MUL ] & (pipe_in_data_i.unit == UNIT_MUL );
    assign unit_sld  = UNITS[UNIT_SLD ] & (pipe_in_data_i.unit == UNIT_SLD );
    assign unit_elem = UNITS[UNIT_ELEM] & (pipe_in_data_i.unit == UNIT_ELEM);

    // identify the type of data that vs2 supplies for ELEM instructions
    logic elem_flush, elem_vs2_data, elem_vs2_mask, elem_vs2_dyn_addr;
    always_comb begin
        elem_flush        = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        elem_vs2_data     = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        elem_vs2_mask     = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        elem_vs2_dyn_addr = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (pipe_in_data_i.mode.elem.op)
            ELEM_XMV:       begin
                elem_flush        = 1'b0;
                elem_vs2_data     = 1'b1;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VPOPC:     begin
                elem_flush        = 1'b0;
                elem_vs2_data     = 1'b0;
                elem_vs2_mask     = 1'b1;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VFIRST:    begin
                elem_flush        = 1'b0;
                elem_vs2_data     = 1'b0;
                elem_vs2_mask     = 1'b1;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VID:       begin
                elem_flush        = 1'b0;
                elem_vs2_data     = 1'b0;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VIOTA:     begin
                elem_flush        = 1'b0;
                elem_vs2_data     = 1'b0;
                elem_vs2_mask     = 1'b1;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VRGATHER:  begin
                elem_flush        = 1'b0;
                elem_vs2_data     = 1'b0;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b1;
            end
            ELEM_VCOMPRESS: begin
                elem_flush        = 1'b1;
                elem_vs2_data     = 1'b0;
                elem_vs2_mask     = 1'b1;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VREDSUM:   begin
                elem_flush        = 1'b1;
                elem_vs2_data     = 1'b1;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VREDAND:   begin
                elem_flush        = 1'b1;
                elem_vs2_data     = 1'b1;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VREDOR:    begin
                elem_flush        = 1'b1;
                elem_vs2_data     = 1'b1;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VREDXOR:   begin
                elem_flush        = 1'b1;
                elem_vs2_data     = 1'b1;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VREDMINU:  begin
                elem_flush        = 1'b1;
                elem_vs2_data     = 1'b1;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VREDMIN:   begin
                elem_flush        = 1'b1;
                elem_vs2_data     = 1'b1;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VREDMAXU:  begin
                elem_flush        = 1'b1;
                elem_vs2_data     = 1'b1;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            ELEM_VREDMAX:   begin
                elem_flush        = 1'b1;
                elem_vs2_data     = 1'b1;
                elem_vs2_mask     = 1'b0;
                elem_vs2_dyn_addr = 1'b0;
            end
            default: ;
        endcase
    end

    // set the initial pipeline state for the incoming instruction
    state_t state_init;
    always_comb begin
        state_init = state_t'('0);

        state_init.count_extra_phase = unit_sld & (pipe_in_data_i.mode.sld.dir == SLD_DOWN);
        state_init.alt_count_init    = '0;
        if (unit_sld) begin
            state_init.alt_count_init = DONT_CARE_ZERO ? '0 : 'x;
            if (pipe_in_data_i.mode.sld.slide1) begin
                if (pipe_in_data_i.mode.sld.dir == SLD_UP) begin
                    // slide counter is all zeroes for up slide, except for a byte slide of 4
                    // when the operand width is 32 bits, then it is 1, since the counter then
                    // captures all but the 2 lowest bits of the byte slide value
                    unique case (pipe_in_data_i.vsew)
                        VSEW_8,
                        VSEW_16: state_init.alt_count_init = '0;
                        VSEW_32: state_init.alt_count_init = {{ALT_COUNT_W-1{1'b0}}, MAX_OP_W == 32};
                        default: ;
                    endcase
                end else begin
                    // slide counter is all ones for down slide, even with a byte slide value of
                    // -4 since this has no effect on any but the 2 lowest bits of the byte
                    // slide value
                    state_init.alt_count_init = {4'b1111, {(ALT_COUNT_W-5){1'b0}}, 1'b1};
                end
            end
            else if (pipe_in_data_i.mode.sld.dir == SLD_UP) begin
                unique case (pipe_in_data_i.vsew)
                    VSEW_8:  state_init.alt_count_init = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(MAX_OP_W/8)   +: ALT_COUNT_W-1]};
                    VSEW_16: state_init.alt_count_init = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(MAX_OP_W/8)-1 +: ALT_COUNT_W-1]};
                    VSEW_32: state_init.alt_count_init = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(MAX_OP_W/8)-2 +: ALT_COUNT_W-1]};
                    default: ;
                endcase
            end else begin
                unique case (pipe_in_data_i.vsew)
                    VSEW_8:  state_init.alt_count_init = ALT_COUNT_W'((
                        {4'b1111, {(ALT_COUNT_W-4){1'b0}}, {$clog2(MAX_OP_W/8){1'b1}}} +
                        {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+2:0]      }
                    ) >> $clog2(MAX_OP_W/8));
                    VSEW_16: state_init.alt_count_init = ALT_COUNT_W'((
                        {4'b1111, {(ALT_COUNT_W-4){1'b0}}, {$clog2(MAX_OP_W/8){1'b1}}} +
                        {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+1:0], 1'b0}
                    ) >> $clog2(MAX_OP_W/8));
                    VSEW_32: state_init.alt_count_init = ALT_COUNT_W'((
                        {4'b1111, {(ALT_COUNT_W-4){1'b0}}, {$clog2(MAX_OP_W/8){1'b1}}} +
                        {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+0:0], 2'b0}
                    ) >> $clog2(MAX_OP_W/8));
                    default: ;
                endcase
            end
        end

        state_init.count_inc = COUNT_INC_MAX;
        if (unit_lsu) begin
            state_init.count_inc = DONT_CARE_ZERO ? count_inc_e'('0) : count_inc_e'('x);
            unique case (pipe_in_data_i.mode.lsu.eew)
                VSEW_8:  state_init.count_inc = COUNT_INC_1;
                VSEW_16: state_init.count_inc = COUNT_INC_2;
                VSEW_32: state_init.count_inc = COUNT_INC_4;
                default: ;
            endcase
            if (pipe_in_data_i.mode.lsu.stride == LSU_UNITSTRIDE) begin
                state_init.count_inc = COUNT_INC_MAX;
            end
        end
        if (unit_elem) begin
            state_init.count_inc = DONT_CARE_ZERO ? count_inc_e'('0) : count_inc_e'('x);
            unique case (pipe_in_data_i.vsew)
                VSEW_8:  state_init.count_inc = COUNT_INC_1;
                VSEW_16: state_init.count_inc = COUNT_INC_2;
                VSEW_32: state_init.count_inc = COUNT_INC_4;
                default: ;
            endcase
        end

        state_init.requires_flush = unit_elem & elem_flush;
        state_init.id             = pipe_in_data_i.id;
        state_init.unit           = pipe_in_data_i.unit;
        state_init.mode           = pipe_in_data_i.mode;
        state_init.emul           = pipe_in_data_i.emul;
        state_init.eew            = unit_lsu ? pipe_in_data_i.mode.lsu.eew : pipe_in_data_i.vsew;
        state_init.vxrm           = pipe_in_data_i.vxrm;
        state_init.vl             = pipe_in_data_i.vl;
        state_init.vl_0           = pipe_in_data_i.vl_0;
        state_init.xval           = pipe_in_data_i.rs1.r.xval;
        if (unit_sld & ~pipe_in_data_i.mode.sld.slide1) begin
            // convert element offset to byte offset for the relevant section of rs1 and negate
            // for down slides
            if (pipe_in_data_i.mode.sld.dir == SLD_UP) begin
                unique case (pipe_in_data_i.vsew)
                    VSEW_8:  state_init.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+2:0]      };
                    VSEW_16: state_init.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                    VSEW_32: state_init.xval[$clog2(VREG_W/8)+3:0] =  {1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                    default: ;
                endcase
            end else begin
                unique case (pipe_in_data_i.vsew)
                    VSEW_8:  state_init.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+2:0]      };
                    VSEW_16: state_init.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+1:0], 1'b0};
                    VSEW_32: state_init.xval[$clog2(VREG_W/8)+3:0] = -{1'b0, pipe_in_data_i.rs1.r.xval[$clog2(VREG_W/8)+0:0], 2'b0};
                    default: ;
                endcase
            end
        end

        for (int i = 0; i < OP_CNT; i++) begin
            state_init.op_flags[i]    = unpack_flags'('0);
        end

        state_init.op_flags[0].vreg   = pipe_in_data_i.rs2.vreg;
        state_init.op_flags[0].narrow = pipe_in_data_i.widenarrow == OP_WIDENING;
        state_init.op_vaddr[0]        = pipe_in_data_i.rs2.r.vaddr;
        state_init.op_xval [0]        = pipe_in_data_i.rs2.r.xval;

        state_init.op_flags[1].vreg   = pipe_in_data_i.rs1.vreg;
        state_init.op_flags[1].narrow = pipe_in_data_i.widenarrow != OP_SINGLEWIDTH;
        state_init.op_vaddr[1]        = pipe_in_data_i.rs1.r.vaddr;
        state_init.op_xval [1]        = pipe_in_data_i.rs1.r.xval;

        state_init.op_flags[OP_CNT-1].vreg = DONT_CARE_ZERO ? 1'b0 : 1'bx;
        unique case (1'b1)
            unit_lsu:  state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.lsu.masked;
            unit_alu:  state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.alu.op_mask != ALU_MASK_NONE;
            unit_mul:  state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.mul.masked;
            unit_sld:  state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.sld.masked;
            unit_elem: state_init.op_flags[OP_CNT-1].vreg = pipe_in_data_i.mode.elem.masked;
            default: ;
        endcase

        state_init.res_vreg  [0] = 1'b1;
        state_init.res_narrow[0] = '0;
        state_init.res_vaddr     = pipe_in_data_i.rd.addr;

        if (unit_lsu) begin
            state_init.op_flags[0       ].elemwise =  pipe_in_data_i.mode.lsu.stride != LSU_UNITSTRIDE;
            state_init.op_flags[1       ].vreg     =  pipe_in_data_i.mode.lsu.store;
            state_init.op_flags[1       ].elemwise =  pipe_in_data_i.mode.lsu.stride != LSU_UNITSTRIDE;
            state_init.op_vaddr[1       ]          =  pipe_in_data_i.rd.addr;
            state_init.op_flags[OP_CNT-1].elemwise =  pipe_in_data_i.mode.lsu.stride != LSU_UNITSTRIDE;
            state_init.res_vreg[0       ]          = ~pipe_in_data_i.mode.lsu.store;
        end
        if (unit_alu) begin
            state_init.op_flags  [0        ].sigext =  pipe_in_data_i.mode.alu.sigext;
            state_init.op_flags  [1        ].sigext =  pipe_in_data_i.mode.alu.sigext;
            state_init.res_vreg  [0        ]        = ~pipe_in_data_i.mode.alu.cmp;
            state_init.res_narrow[0        ]        =  pipe_in_data_i.widenarrow == OP_NARROWING;
            state_init.res_vreg  [RES_CNT-1]        =  pipe_in_data_i.mode.alu.cmp;
        end
        if (unit_mul) begin
            state_init.op_vaddr[0]                          = pipe_in_data_i.mode.mul.op2_is_vd ? pipe_in_data_i.rd.addr : pipe_in_data_i.rs2.r.vaddr;
            state_init.op_flags[0].sigext                   = pipe_in_data_i.mode.mul.op2_signed;
            state_init.op_flags[1].sigext                   = pipe_in_data_i.mode.mul.op1_signed;
            state_init.op_flags[(OP_CNT >= 3) ? 2 : 0].vreg = pipe_in_data_i.mode.mul.op == MUL_VMACC;
            state_init.op_vaddr[(OP_CNT >= 3) ? 2 : 0]      = pipe_in_data_i.mode.mul.op2_is_vd ? pipe_in_data_i.rs2.r.vaddr : pipe_in_data_i.rd.addr;
        end
        if (unit_elem) begin
            state_init.op_flags[0                           ].vreg     = pipe_in_data_i.rs2.vreg & elem_vs2_data;
            state_init.op_flags[0                           ].elemwise = 1'b1;
            state_init.op_flags[0                           ].sigext   = pipe_in_data_i.mode.elem.sigext;
            state_init.op_flags[1                           ].elemwise = 1'b1;
            state_init.op_flags[1                           ].narrow   = 1'b0; // only op 0 can be narrow
            state_init.op_flags[(OP_CNT >= 3) ? OP_CNT-3 : 0].vreg     = elem_vs2_dyn_addr;
            state_init.op_vaddr[(OP_CNT >= 3) ? OP_CNT-3 : 0]          = pipe_in_data_i.rs2.r.vaddr;
            state_init.op_flags[                OP_CNT-2    ].vreg     = pipe_in_data_i.rs2.vreg & elem_vs2_mask;
            state_init.op_flags[                OP_CNT-2    ].elemwise = 1'b1;
            state_init.op_vaddr[                OP_CNT-2    ]          = pipe_in_data_i.rs2.r.vaddr;
            state_init.op_flags[                OP_CNT-1    ].elemwise = 1'b1;
        end
    end


    ///////////////////////////////////////////////////////////////////////////
    // PIPELINE INSTANTIATION

    generate
        if (OP_CNT == 2 && RES_CNT == 1) begin
            localparam int unsigned OP_W           [2] = '{MAX_OP_W, MAX_OP_W/8};
            localparam int unsigned OP_STAGE       [2] = '{1, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC         [2] = '{0, VPORT_CNT};
            localparam bit [1:0]    OP_DYN_ADDR        = '0;
            localparam bit [1:0]    OP_MASK            = 2'b10;
            localparam bit [1:0]    OP_XREG            = '0;
            localparam bit [1:0]    OP_NARROW          = {1'b0, OP0_NARROW};
            localparam bit [1:0]    OP_ALLOW_ELEMWISE  = {OPMASK_ELEMWISE, OP0_ELEMWISE};
            localparam bit [1:0]    OP_ALWAYS_ELEMWISE = '0;
            localparam bit [1:0]    OP_ALT_COUNTER     = {1'b0, OP0_ALT_COUNTER};

            localparam int unsigned RES_W           [1] = '{MAX_RES_W};
            localparam bit [0:0]    RES_ALWAYS_VREG     = RES0_ALWAYS_VREG;
            localparam bit [0:0]    RES_MASK            = '0;
            localparam bit [0:0]    RES_NARROW          = RES0_NARROW;
            localparam bit [0:0]    RES_ALLOW_ELEMWISE  = RES0_ALLOW_ELEMWISE;

            vproc_pipeline #(
                .VREG_W              ( VREG_W              ),
                .CFG_VL_W            ( CFG_VL_W            ),
                .XIF_ID_W            ( XIF_ID_W            ),
                .XIF_ID_CNT          ( XIF_ID_CNT          ),
                .UNITS               ( UNITS               ),
                .MAX_VPORT_W         ( MAX_VPORT_W         ),
                .MAX_VADDR_W         ( MAX_VADDR_W         ),
                .VPORT_CNT           ( VPORT_CNT           ),
                .VPORT_W             ( VPORT_W             ),
                .VADDR_W             ( VADDR_W             ),
                .VPORT_BUFFER        ( VPORT_BUFFER        ),
                .MAX_OP_W            ( MAX_OP_W            ),
                .OP_CNT              ( OP_CNT              ),
                .OP_W                ( OP_W                ),
                .OP_STAGE            ( OP_STAGE            ),
                .OP_SRC              ( OP_SRC              ),
                .OP_DYN_ADDR_SRC     ( 1                   ),
                .OP_DYN_ADDR         ( OP_DYN_ADDR         ),
                .OP_MASK             ( OP_MASK             ),
                .OP_XREG             ( OP_XREG             ),
                .OP_NARROW           ( OP_NARROW           ),
                .OP_ALLOW_ELEMWISE   ( OP_ALLOW_ELEMWISE   ),
                .OP_ALWAYS_ELEMWISE  ( OP_ALWAYS_ELEMWISE  ),
                .OP_ALT_COUNTER      ( OP_ALT_COUNTER      ),
                .OP_ALWAYS_VREG      ( '0                  ),
                .UNPACK_STAGES       ( UNPACK_STAGES       ),
                .MAX_RES_W           ( MAX_RES_W           ),
                .RES_CNT             ( RES_CNT             ),
                .RES_W               ( RES_W               ),
                .RES_MASK            ( RES_MASK            ),
                .RES_NARROW          ( RES_NARROW          ),
                .RES_ALLOW_ELEMWISE  ( RES_ALLOW_ELEMWISE  ),
                .RES_ALWAYS_ELEMWISE ( '0                  ),
                .RES_ALWAYS_VREG     ( RES_ALWAYS_VREG     ),
                .MAY_FLUSH           ( MAY_FLUSH           ),
                .MUL_TYPE            ( MUL_TYPE            ),
                .ADDR_ALIGNED        ( ADDR_ALIGNED        ),
                .MAX_WR_ATTEMPTS     ( MAX_WR_ATTEMPTS     ),
                .INIT_STATE_T        ( state_t             ),
                .DONT_CARE_ZERO      ( DONT_CARE_ZERO      )
            ) pipeline (
                .pipe_in_state_i     ( state_init          ),
                .*
            );
        end
        else if (OP_CNT == 3 && RES_CNT == 1) begin
            localparam int unsigned OP_W           [3] = '{MAX_OP_W, MAX_OP_W, MAX_OP_W/8};
            localparam int unsigned OP_STAGE       [3] = '{1, 2, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC         [3] = '{0, 0, VPORT_CNT};
            localparam bit [2:0]    OP_DYN_ADDR        = '0;
            localparam bit [2:0]    OP_MASK            = 3'b100;
            localparam bit [2:0]    OP_XREG            = {1'b0, OP1_XREG, 1'b0};
            localparam bit [2:0]    OP_NARROW          = {1'b0, OP1_NARROW, OP0_NARROW};
            localparam bit [2:0]    OP_ALLOW_ELEMWISE  = {OPMASK_ELEMWISE, OP1_ELEMWISE, OP0_ELEMWISE};
            localparam bit [2:0]    OP_ALWAYS_ELEMWISE = '0;
            localparam bit [2:0]    OP_ALT_COUNTER     = {2'b0, OP0_ALT_COUNTER};

            localparam int unsigned RES_W           [1] = '{MAX_RES_W};
            localparam bit [0:0]    RES_ALWAYS_VREG     = RES0_ALWAYS_VREG;
            localparam bit [0:0]    RES_MASK            = '0;
            localparam bit [0:0]    RES_NARROW          = RES0_NARROW;
            localparam bit [0:0]    RES_ALLOW_ELEMWISE  = RES0_ALLOW_ELEMWISE;

            vproc_pipeline #(
                .VREG_W              ( VREG_W              ),
                .CFG_VL_W            ( CFG_VL_W            ),
                .XIF_ID_W            ( XIF_ID_W            ),
                .XIF_ID_CNT          ( XIF_ID_CNT          ),
                .UNITS               ( UNITS               ),
                .MAX_VPORT_W         ( MAX_VPORT_W         ),
                .MAX_VADDR_W         ( MAX_VADDR_W         ),
                .VPORT_CNT           ( VPORT_CNT           ),
                .VPORT_W             ( VPORT_W             ),
                .VADDR_W             ( VADDR_W             ),
                .VPORT_BUFFER        ( VPORT_BUFFER        ),
                .MAX_OP_W            ( MAX_OP_W            ),
                .OP_CNT              ( OP_CNT              ),
                .OP_W                ( OP_W                ),
                .OP_STAGE            ( OP_STAGE            ),
                .OP_SRC              ( OP_SRC              ),
                .OP_DYN_ADDR_SRC     ( 1                   ),
                .OP_DYN_ADDR         ( OP_DYN_ADDR         ),
                .OP_MASK             ( OP_MASK             ),
                .OP_XREG             ( OP_XREG             ),
                .OP_NARROW           ( OP_NARROW           ),
                .OP_ALLOW_ELEMWISE   ( OP_ALLOW_ELEMWISE   ),
                .OP_ALWAYS_ELEMWISE  ( OP_ALWAYS_ELEMWISE  ),
                .OP_ALT_COUNTER      ( OP_ALT_COUNTER      ),
                .OP_ALWAYS_VREG      ( '0                  ),
                .UNPACK_STAGES       ( UNPACK_STAGES       ),
                .MAX_RES_W           ( MAX_RES_W           ),
                .RES_CNT             ( RES_CNT             ),
                .RES_W               ( RES_W               ),
                .RES_MASK            ( RES_MASK            ),
                .RES_NARROW          ( RES_NARROW          ),
                .RES_ALLOW_ELEMWISE  ( RES_ALLOW_ELEMWISE  ),
                .RES_ALWAYS_ELEMWISE ( '0                  ),
                .RES_ALWAYS_VREG     ( RES_ALWAYS_VREG     ),
                .MAY_FLUSH           ( MAY_FLUSH           ),
                .MUL_TYPE            ( MUL_TYPE            ),
                .ADDR_ALIGNED        ( ADDR_ALIGNED        ),
                .MAX_WR_ATTEMPTS     ( MAX_WR_ATTEMPTS     ),
                .INIT_STATE_T        ( state_t             ),
                .DONT_CARE_ZERO      ( DONT_CARE_ZERO      )
            ) pipeline (
                .pipe_in_state_i     ( state_init          ),
                .*
            );
        end
        else if (OP_CNT == 3 && RES_CNT == 2) begin
            localparam int unsigned OP_W           [3] = '{MAX_OP_W, MAX_OP_W, MAX_OP_W/8};
            localparam int unsigned OP_STAGE       [3] = '{1, 2, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC         [3] = '{0, 0, VPORT_CNT};
            localparam bit [2:0]    OP_DYN_ADDR        = '0;
            localparam bit [2:0]    OP_MASK            = 3'b100;
            localparam bit [2:0]    OP_XREG            = {1'b0, OP1_XREG, 1'b0};
            localparam bit [2:0]    OP_NARROW          = {1'b0, OP1_NARROW, OP0_NARROW};
            localparam bit [2:0]    OP_ALLOW_ELEMWISE  = {OPMASK_ELEMWISE, OP1_ELEMWISE, OP0_ELEMWISE};
            localparam bit [2:0]    OP_ALWAYS_ELEMWISE = '0;
            localparam bit [2:0]    OP_ALT_COUNTER     = {2'b0, OP0_ALT_COUNTER};

            localparam int unsigned RES_W           [2] = '{MAX_RES_W, MAX_RES_W/8};
            localparam bit [1:0]    RES_ALWAYS_VREG     = {1'b0, RES0_ALWAYS_VREG};
            localparam bit [1:0]    RES_MASK            = 2'b10;
            localparam bit [1:0]    RES_NARROW          = {1'b0, RES0_NARROW};
            localparam bit [1:0]    RES_ALLOW_ELEMWISE  = {1'b0, RES0_ALLOW_ELEMWISE};

            vproc_pipeline #(
                .VREG_W              ( VREG_W              ),
                .CFG_VL_W            ( CFG_VL_W            ),
                .XIF_ID_W            ( XIF_ID_W            ),
                .XIF_ID_CNT          ( XIF_ID_CNT          ),
                .UNITS               ( UNITS               ),
                .MAX_VPORT_W         ( MAX_VPORT_W         ),
                .MAX_VADDR_W         ( MAX_VADDR_W         ),
                .VPORT_CNT           ( VPORT_CNT           ),
                .VPORT_W             ( VPORT_W             ),
                .VADDR_W             ( VADDR_W             ),
                .VPORT_BUFFER        ( VPORT_BUFFER        ),
                .MAX_OP_W            ( MAX_OP_W            ),
                .OP_CNT              ( OP_CNT              ),
                .OP_W                ( OP_W                ),
                .OP_STAGE            ( OP_STAGE            ),
                .OP_SRC              ( OP_SRC              ),
                .OP_DYN_ADDR_SRC     ( 1                   ),
                .OP_DYN_ADDR         ( OP_DYN_ADDR         ),
                .OP_MASK             ( OP_MASK             ),
                .OP_XREG             ( OP_XREG             ),
                .OP_NARROW           ( OP_NARROW           ),
                .OP_ALLOW_ELEMWISE   ( OP_ALLOW_ELEMWISE   ),
                .OP_ALWAYS_ELEMWISE  ( OP_ALWAYS_ELEMWISE  ),
                .OP_ALT_COUNTER      ( OP_ALT_COUNTER      ),
                .OP_ALWAYS_VREG      ( '0                  ),
                .UNPACK_STAGES       ( UNPACK_STAGES       ),
                .MAX_RES_W           ( MAX_RES_W           ),
                .RES_CNT             ( RES_CNT             ),
                .RES_W               ( RES_W               ),
                .RES_MASK            ( RES_MASK            ),
                .RES_NARROW          ( RES_NARROW          ),
                .RES_ALLOW_ELEMWISE  ( RES_ALLOW_ELEMWISE  ),
                .RES_ALWAYS_ELEMWISE ( '0                  ),
                .RES_ALWAYS_VREG     ( RES_ALWAYS_VREG     ),
                .MAY_FLUSH           ( MAY_FLUSH           ),
                .MUL_TYPE            ( MUL_TYPE            ),
                .ADDR_ALIGNED        ( ADDR_ALIGNED        ),
                .MAX_WR_ATTEMPTS     ( MAX_WR_ATTEMPTS     ),
                .INIT_STATE_T        ( state_t             ),
                .DONT_CARE_ZERO      ( DONT_CARE_ZERO      )
            ) pipeline (
                .pipe_in_state_i     ( state_init          ),
                .*
            );
        end
        else if (OP_CNT == 4 && RES_CNT == 1) begin
            localparam int unsigned OP_W           [4] = '{MAX_OP_W, MAX_OP_W, MAX_OP_W, MAX_OP_W/8};
            localparam int unsigned OP_STAGE       [4] = '{1, 2, UNPACK_STAGES-1, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC         [4] = '{0, 0, VPORT_CNT-1, VPORT_CNT};
            localparam bit [3:0]    OP_DYN_ADDR        = '0;
            localparam bit [3:0]    OP_MASK            = 4'b1000;
            localparam bit [3:0]    OP_XREG            = {2'b0, OP1_XREG, 1'b0};
            localparam bit [3:0]    OP_NARROW          = {2'b0, OP1_NARROW, OP0_NARROW};
            localparam bit [3:0]    OP_ALLOW_ELEMWISE  = {OPMASK_ELEMWISE, 1'b0, OP1_ELEMWISE, OP0_ELEMWISE};
            localparam bit [3:0]    OP_ALWAYS_ELEMWISE = '0;
            localparam bit [3:0]    OP_ALT_COUNTER     = {3'b0, OP0_ALT_COUNTER};

            localparam int unsigned RES_W           [1] = '{MAX_RES_W};
            localparam bit [0:0]    RES_ALWAYS_VREG     = RES0_ALWAYS_VREG;
            localparam bit [0:0]    RES_MASK            = '0;
            localparam bit [0:0]    RES_NARROW          = RES0_NARROW;
            localparam bit [0:0]    RES_ALLOW_ELEMWISE  = RES0_ALLOW_ELEMWISE;

            vproc_pipeline #(
                .VREG_W              ( VREG_W              ),
                .CFG_VL_W            ( CFG_VL_W            ),
                .XIF_ID_W            ( XIF_ID_W            ),
                .XIF_ID_CNT          ( XIF_ID_CNT          ),
                .UNITS               ( UNITS               ),
                .MAX_VPORT_W         ( MAX_VPORT_W         ),
                .MAX_VADDR_W         ( MAX_VADDR_W         ),
                .VPORT_CNT           ( VPORT_CNT           ),
                .VPORT_W             ( VPORT_W             ),
                .VADDR_W             ( VADDR_W             ),
                .VPORT_BUFFER        ( VPORT_BUFFER        ),
                .MAX_OP_W            ( MAX_OP_W            ),
                .OP_CNT              ( OP_CNT              ),
                .OP_W                ( OP_W                ),
                .OP_STAGE            ( OP_STAGE            ),
                .OP_SRC              ( OP_SRC              ),
                .OP_DYN_ADDR_SRC     ( 1                   ),
                .OP_DYN_ADDR         ( OP_DYN_ADDR         ),
                .OP_MASK             ( OP_MASK             ),
                .OP_XREG             ( OP_XREG             ),
                .OP_NARROW           ( OP_NARROW           ),
                .OP_ALLOW_ELEMWISE   ( OP_ALLOW_ELEMWISE   ),
                .OP_ALWAYS_ELEMWISE  ( OP_ALWAYS_ELEMWISE  ),
                .OP_ALT_COUNTER      ( OP_ALT_COUNTER      ),
                .OP_ALWAYS_VREG      ( '0                  ),
                .UNPACK_STAGES       ( UNPACK_STAGES       ),
                .MAX_RES_W           ( MAX_RES_W           ),
                .RES_CNT             ( RES_CNT             ),
                .RES_W               ( RES_W               ),
                .RES_MASK            ( RES_MASK            ),
                .RES_NARROW          ( RES_NARROW          ),
                .RES_ALLOW_ELEMWISE  ( RES_ALLOW_ELEMWISE  ),
                .RES_ALWAYS_ELEMWISE ( '0                  ),
                .RES_ALWAYS_VREG     ( RES_ALWAYS_VREG     ),
                .MAY_FLUSH           ( MAY_FLUSH           ),
                .MUL_TYPE            ( MUL_TYPE            ),
                .ADDR_ALIGNED        ( ADDR_ALIGNED        ),
                .MAX_WR_ATTEMPTS     ( MAX_WR_ATTEMPTS     ),
                .INIT_STATE_T        ( state_t             ),
                .DONT_CARE_ZERO      ( DONT_CARE_ZERO      )
            ) pipeline (
                .pipe_in_state_i     ( state_init          ),
                .*
            );
        end
        else if (OP_CNT == 5 && RES_CNT == 1) begin
            localparam int unsigned OP_W           [5] = '{MAX_OP_W, MAX_OP_W, MAX_OP_W, 1, MAX_OP_W/8};
            // TODO it appears as if fetching operands 1 and -3 could collide
            localparam int unsigned OP_STAGE       [5] = '{2, 1, 3, 2, UNPACK_STAGES-1};
            localparam int unsigned OP_SRC         [5] = '{0, 0, VPORT_CNT-1, 0, VPORT_CNT};
            localparam bit [4:0]    OP_DYN_ADDR        = OP_DYN_ADDR_OFFSET ? 5'b00100 : '0;
            localparam bit [4:0]    OP_MASK            = OP_SECOND_MASK ? 5'b11000 : 5'b10000;
            localparam bit [4:0]    OP_XREG            = {3'b0, OP1_XREG, 1'b0};
            localparam bit [4:0]    OP_NARROW          = {3'b0, OP1_NARROW, OP0_NARROW};
            localparam bit [4:0]    OP_ALLOW_ELEMWISE  = {OPMASK_ELEMWISE, 2'b0, OP1_ELEMWISE, OP0_ELEMWISE};
            localparam bit [4:0]    OP_ALWAYS_ELEMWISE = {1'b0, OP_SECOND_MASK, 3'b0};
            localparam bit [4:0]    OP_ALT_COUNTER     = {4'b0, OP0_ALT_COUNTER};

            localparam int unsigned RES_W           [1] = '{MAX_RES_W};
            localparam bit [0:0]    RES_ALWAYS_VREG     = RES0_ALWAYS_VREG;
            localparam bit [0:0]    RES_MASK            = '0;
            localparam bit [0:0]    RES_NARROW          = RES0_NARROW;
            localparam bit [0:0]    RES_ALLOW_ELEMWISE  = RES0_ALLOW_ELEMWISE;

            vproc_pipeline #(
                .VREG_W              ( VREG_W              ),
                .CFG_VL_W            ( CFG_VL_W            ),
                .XIF_ID_W            ( XIF_ID_W            ),
                .XIF_ID_CNT          ( XIF_ID_CNT          ),
                .UNITS               ( UNITS               ),
                .MAX_VPORT_W         ( MAX_VPORT_W         ),
                .MAX_VADDR_W         ( MAX_VADDR_W         ),
                .VPORT_CNT           ( VPORT_CNT           ),
                .VPORT_W             ( VPORT_W             ),
                .VADDR_W             ( VADDR_W             ),
                .VPORT_BUFFER        ( VPORT_BUFFER        ),
                .MAX_OP_W            ( MAX_OP_W            ),
                .OP_CNT              ( OP_CNT              ),
                .OP_W                ( OP_W                ),
                .OP_STAGE            ( OP_STAGE            ),
                .OP_SRC              ( OP_SRC              ),
                .OP_DYN_ADDR_SRC     ( 1                   ),
                .OP_DYN_ADDR         ( OP_DYN_ADDR         ),
                .OP_MASK             ( OP_MASK             ),
                .OP_XREG             ( OP_XREG             ),
                .OP_NARROW           ( OP_NARROW           ),
                .OP_ALLOW_ELEMWISE   ( OP_ALLOW_ELEMWISE   ),
                .OP_ALWAYS_ELEMWISE  ( OP_ALWAYS_ELEMWISE  ),
                .OP_ALT_COUNTER      ( OP_ALT_COUNTER      ),
                .OP_ALWAYS_VREG      ( '0                  ),
                .UNPACK_STAGES       ( UNPACK_STAGES       ),
                .MAX_RES_W           ( MAX_RES_W           ),
                .RES_CNT             ( RES_CNT             ),
                .RES_W               ( RES_W               ),
                .RES_MASK            ( RES_MASK            ),
                .RES_NARROW          ( RES_NARROW          ),
                .RES_ALLOW_ELEMWISE  ( RES_ALLOW_ELEMWISE  ),
                .RES_ALWAYS_ELEMWISE ( '0                  ),
                .RES_ALWAYS_VREG     ( RES_ALWAYS_VREG     ),
                .MAY_FLUSH           ( MAY_FLUSH           ),
                .MUL_TYPE            ( MUL_TYPE            ),
                .ADDR_ALIGNED        ( ADDR_ALIGNED        ),
                .MAX_WR_ATTEMPTS     ( MAX_WR_ATTEMPTS     ),
                .INIT_STATE_T        ( state_t             ),
                .DONT_CARE_ZERO      ( DONT_CARE_ZERO      )
            ) pipeline (
                .pipe_in_state_i     ( state_init          ),
                .*
            );
        end
    endgenerate

endmodule
