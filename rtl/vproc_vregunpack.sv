// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


// Unpacking vector registers to operands
module vproc_vregunpack
    #(
        // vector register ports configuration
        parameter int unsigned                        MAX_VPORT_W        = 128,  // max port width
        parameter int unsigned                        MAX_VADDR_W        = 5,    // max addr width
        parameter int unsigned                        VPORT_CNT          = 1,    // port count
        parameter int unsigned                        VPORT_W[VPORT_CNT] = '{0}, // port widths
        parameter int unsigned                        VADDR_W[VPORT_CNT] = '{5}, // address widths
        parameter bit [VPORT_CNT-1:0]                 VPORT_ADDR_ZERO    = '0,   // set addr to 0
        parameter bit [VPORT_CNT-1:0]                 VPORT_BUFFER       = '0,   // buffer port

        // vector register operands configuration
        parameter int unsigned                        MAX_OP_W           = 64,   // max op width
        parameter int unsigned                        OP_CNT             = 1,    // op count
        parameter int unsigned                        OP_W    [OP_CNT]   = '{0}, // op widths
        parameter int unsigned                        OP_STAGE[OP_CNT]   = '{0}, // op load stage
        parameter int unsigned                        OP_SRC  [OP_CNT]   = '{0}, // op port index
        parameter bit [OP_CNT-1:0]                    OP_ADDR_OFFSET_OP0 = '0,   // offset op addr
        parameter bit [OP_CNT-1:0]                    OP_MASK            = '0,   // op is a mask
        parameter bit [OP_CNT-1:0]                    OP_XREG            = '0,   // op may be XREG
        parameter bit [OP_CNT-1:0]                    OP_NARROW          = '0,   // op may be narrow
        parameter bit [OP_CNT-1:0]                    OP_ALLOW_ELEMWISE  = '0,   // op may be 1 elem
        parameter bit [OP_CNT-1:0]                    OP_ALWAYS_ELEMWISE = '0,   // op is 1 elem
        parameter bit [OP_CNT-1:0]                    OP_HOLD_FLAG       = '0,   // allow hold of op

        parameter int unsigned                        UNPACK_STAGES      = 2,    // stage count
        parameter type                                FLAGS_T            = logic,// load struct type
        parameter int unsigned                        CTRL_DATA_W        = 0,    // ctrl data width
        parameter bit                                 DONT_CARE_ZERO     = 1'b0  // set don't care 0
    )(
        input  logic                                  clk_i,
        input  logic                                  async_rst_ni,
        input  logic                                  sync_rst_ni,

        // vector register file read ports
        output logic [VPORT_CNT-1:0][MAX_VADDR_W-1:0] vreg_rd_addr_o,       // vreg read address
        input  logic [VPORT_CNT-1:0][MAX_VPORT_W-1:0] vreg_rd_data_i,       // vreg read data

        // pipeline in
        input  logic                                  pipe_in_valid_i,
        output logic                                  pipe_in_ready_o,
        input  logic               [CTRL_DATA_W-1:0]  pipe_in_ctrl_i,       // pipeline control sigs
        input  vproc_pkg::cfg_vsew                    pipe_in_eew_i,        // current element width
        input  FLAGS_T [OP_CNT-1:0]                   pipe_in_op_flags_i,   // unpack flags of ops
        input  logic   [OP_CNT-1:0][MAX_VADDR_W-1:0]  pipe_in_op_vaddr_i,   // vreg addresses of ops
        input  logic   [OP_CNT-1:0][31           :0]  pipe_in_op_xval_i,    // X reg values for ops

        // pipeline out
        output logic                                  pipe_out_valid_o,
        input  logic                                  pipe_out_ready_i,
        output logic               [CTRL_DATA_W-1:0]  pipe_out_ctrl_o,      // pipeline control sigs
        output logic   [OP_CNT-1:0][MAX_OP_W   -1:0]  pipe_out_op_data_o,   // unpacked operands

        // pending vector register read mask
        output logic [(1<<MAX_VADDR_W)-1:0]           pending_vreg_reads_o,

        // stage valid and control signals flags
        output logic                                  stage_valid_any_o,
        output logic [CTRL_DATA_W-1:0]                ctrl_flags_any_o,
        output logic [CTRL_DATA_W-1:0]                ctrl_flags_all_o
    );

    import vproc_pkg::*;

    generate
        for (genvar i = 0; i < VPORT_CNT; i++) begin
            if (VPORT_W[i] > MAX_VPORT_W) begin
                $fatal(1, "Vector register read port %d is %d bits wide, exceeds maximum of %d",
                          i, VPORT_W[i], MAX_VPORT_W);
            end
            if (VADDR_W[i] > MAX_VADDR_W) begin
                $fatal(1, "Vector register read port %d has %d address bits, exceeds maximum of %d",
                          i, VADDR_W[i], MAX_VADDR_W);
            end
        end
        for (genvar i = 0; i < OP_CNT; i++) begin
            if (OP_W[i] > MAX_OP_W) begin
                $fatal(1, "Operand %d has a width of %d bits, exceeds maximum of %d",
                          i, OP_W[i], MAX_OP_W);
            end
            if (OP_STAGE[i] + 1 > UNPACK_STAGES) begin
                $fatal(1, "Operand %d load stage %d is invalid (unpack has %d stages)",
                          i, OP_STAGE[i], UNPACK_STAGES);
            end
            if (OP_SRC[i] >= VPORT_CNT) begin
                $fatal(1, "Operand %d source index %d is invalid (%d vreg read ports available)",
                          i, OP_SRC[i], VPORT_CNT);
            end
        end
    endgenerate

    typedef struct packed {
        logic               [CTRL_DATA_W-1:0] ctrl;
        cfg_vsew                              eew;
        FLAGS_T [OP_CNT-1:0]                  op_flags;
        logic   [OP_CNT-1:0][MAX_VADDR_W-1:0] op_vaddr;
        logic   [OP_CNT-1:0][31           :0] op_xval;
        logic   [OP_CNT-1:0][MAX_VPORT_W-1:0] op_buffer;
        logic   [OP_CNT-1:0][MAX_OP_W   -1:0] op_data;
    } vregunpack_state_t;

    vregunpack_state_t stage_0;
    always_comb begin
        stage_0            = vregunpack_state_t'(DONT_CARE_ZERO ? '0 : 'x);
        stage_0.ctrl       = pipe_in_ctrl_i;
        stage_0.eew        = pipe_in_eew_i;
        stage_0.op_flags   = pipe_in_op_flags_i;
        stage_0.op_vaddr   = pipe_in_op_vaddr_i;
        stage_0.op_xval    = pipe_in_op_xval_i;
    end

    // Unpack stage signals.  Note that stage 0 gets assigned the input values and hence is not an
    // actual stage.  Thus, there are intentionally one more valid, ready, and state signals than
    // actual stages.
    logic              [UNPACK_STAGES:0] stage_valid, stage_valid_q, stage_valid_d;
    vregunpack_state_t [UNPACK_STAGES:0] stage_state, stage_state_q, stage_state_d;
    logic              [UNPACK_STAGES:0] stage_ready;

    always_ff @(posedge clk_i or negedge async_rst_ni) begin
        if (~async_rst_ni) begin
            stage_valid_q <= '0;
        end
        else if (~sync_rst_ni) begin
            stage_valid_q <= '0;
        end
        else begin
            stage_valid_q <= stage_valid_d;
        end
    end
    always_ff @(posedge clk_i) begin
        stage_state_q <= stage_state_d;
    end

    always_comb begin
        stage_valid[0] = pipe_in_valid_i;
        stage_state[0] = stage_0;
        for (int i = 1; i < UNPACK_STAGES + 1; i++) begin
            stage_valid[i] = stage_valid_q[i];
            stage_state[i] = stage_state_q[i];
        end
    end

    // Operand buffers next-state signal and extracted operand data
    logic [OP_CNT-1:0][MAX_VPORT_W-1:0] op_buffer_next;
    logic [OP_CNT-1:0][MAX_OP_W   -1:0] op_data;

    always_comb begin
        stage_valid_d = stage_valid_q;
        stage_state_d = stage_state_q;
        for (int i = 1; i < UNPACK_STAGES + 1; i++) begin
            if (stage_ready[i]) begin
                stage_valid_d[i] = (i == 1) ? pipe_in_valid_i : stage_valid_q[i-1];
                stage_state_d[i] = (i == 1) ? stage_0         : stage_state_q[i-1];

                // operand buffer is part of the stage after the respective vreg load
                for (int j = 0; j < OP_CNT; j++) begin
                    if (i == OP_STAGE[j] + 1) begin
                        stage_state_d[i].op_buffer[j] = op_buffer_next[j];
                    end
                end

                // unpacked operands are buffered starting from two stages after the respective
                // vreg load
                for (int j = 0; j < OP_CNT; j++) begin
                    if (i == OP_STAGE[j] + 2) begin
                        stage_state_d[i].op_data[j] = op_data[j];
                    end
                end
            end
        end
    end

    always_comb begin
        // None of the unpack stages can stall by itself, hence all the stages are ready if the
        // output pipe is ready.  Additionally any stage that is not currently valid is also ready
        // to accept new data.  However, this might create problems if buffered vector register
        // ports have inconsistent ready conditions when being loaded by different operands in
        // different stages.  To avoid troubles, all stages are only ready when the output pipe is
        // ready if any of the vector register ports is being buffered.
        stage_ready = {(UNPACK_STAGES+1){pipe_out_ready_i}};
        if (VPORT_BUFFER == '0) begin
            for (int i = 0; i < UNPACK_STAGES; i++) begin
                for (int j = i; j < UNPACK_STAGES; j++) begin
                    if (~stage_valid[j]) begin
                        // A stage is ready if the next stage is ready or if it is invalid, which
                        // implies that a stage is also ready if any subsequent stage is invalid.
                        stage_ready[i] = 1'b1;
                    end
                end
            end
        end
    end

    always_comb begin
        pipe_in_ready_o    = stage_ready[0];
        pipe_out_valid_o   = stage_valid[UNPACK_STAGES];
        pipe_out_ctrl_o    = stage_state[UNPACK_STAGES].ctrl;
        pipe_out_op_data_o = stage_state[UNPACK_STAGES].op_data;
        // make operands that have just been unpacked available to the output pipe
        for (int i = 0; i < OP_CNT; i++) begin
            if (OP_STAGE[i] + 1 == UNPACK_STAGES) begin
                pipe_out_op_data_o[i] = op_data[i];
            end
        end
    end

    // Addressing signals and vreg addresses of operands and masks;  addressing takes place in the
    // stage prior to loading the operand buffer if the respective vreg is buffered and in the same
    // stage otherwise.
    logic [OP_CNT-1:0]                  op_addressing;
    logic [OP_CNT-1:0][MAX_VADDR_W-1:0] op_vreg_addr;
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            localparam int unsigned ADDR_STAGE = VPORT_BUFFER[OP_SRC[i]] ? OP_STAGE[i] - 1 :
                                                                           OP_STAGE[i];
            assign op_addressing[i] = stage_valid[ADDR_STAGE] &
                                      stage_state[ADDR_STAGE].op_flags[i].load &
                                      (~OP_XREG[i] | stage_state[ADDR_STAGE].op_flags[i].vreg);
            if (OP_ADDR_OFFSET_OP0[i]) begin
                // get address offset from operand 0
                logic [OP_W[0]-1:0] op0_data;
                assign op0_data = (OP_STAGE[0] + 1 == ADDR_STAGE) ? op_data[0][OP_W[0]-1:0] :
                                            stage_state[ADDR_STAGE].op_data[0][OP_W[0]-1:0];
                logic [31:0] op0_addr_offset;
                always_comb begin
                    op0_addr_offset = DONT_CARE_ZERO ? '0 : 'x;
                    unique case (stage_state[ADDR_STAGE].eew)
                        VSEW_8:  op0_addr_offset = {24'b0, op0_data[7 :0]      };
                        VSEW_16: op0_addr_offset = {15'b0, op0_data[15:0], 1'b0};
                        VSEW_32: op0_addr_offset = {       op0_data[29:0], 2'b0};
                        default: ;
                    endcase
                end
                // the address offset may be used to address up to 1/4 of the available vector
                // register space and is OR-ed with the specified base address
                assign op_vreg_addr[i] = stage_state[ADDR_STAGE].op_vaddr[i] | {2'b0,
                    op0_addr_offset[$clog2(VPORT_W[OP_SRC[i]]/8 ) +: VADDR_W[OP_SRC[i]]-2],
                    {(MAX_VADDR_W-VADDR_W[OP_SRC[i]]){1'b0}}
                };
            end else begin
                assign op_vreg_addr[i] = stage_state[ADDR_STAGE].op_vaddr[i];
            end
        end
    endgenerate

    // Vreg addressing
    generate
        for (genvar i = 0; i < VPORT_CNT; i++) begin
            always_comb begin
                if (VPORT_ADDR_ZERO[i]) begin
                    vreg_rd_addr_o[i] = '0;
                end else begin
                    vreg_rd_addr_o[i] = DONT_CARE_ZERO ? '0 : 'x;
                    for (int j = 0; j < OP_CNT; j++) begin
                        if ((i == OP_SRC[j]) & op_addressing[j]) begin
                            vreg_rd_addr_o[i] = {
                                op_vreg_addr[j][MAX_VADDR_W-1:MAX_VADDR_W-VADDR_W[i]],
                                {(MAX_VADDR_W-VADDR_W[i]){1'b0}}
                            };
                        end
                    end
                end
            end
        end
    endgenerate

    // Vreg buffering
    logic [VPORT_CNT-1:0][MAX_VPORT_W-1:0] vreg_buffer_q, vreg_buffer_d;
    always_ff @(posedge clk_i) begin
        vreg_buffer_q <= vreg_buffer_d;
    end
    always_comb begin
        vreg_buffer_d = vreg_buffer_q;
        for (int i = 0; i < VPORT_CNT; i++) begin
            // Ensure consistent ready signals by using the output pipe ready signal for all stages
            // and for buffering vector register ports if any vector register port is buffered.
            if (pipe_out_ready_i) begin
                vreg_buffer_d[i] = vreg_rd_data_i[i];
            end
        end
    end

    // Vector register values of operands
    logic [OP_CNT-1:0][MAX_VPORT_W-1:0] op_vreg_data;
    always_comb begin
        for (int i = 0; i < OP_CNT; i++) begin
            op_vreg_data[i] = VPORT_BUFFER[OP_SRC[i]] ? vreg_buffer_q [OP_SRC[i]] :
                                                        vreg_rd_data_i[OP_SRC[i]];
        end
    end

    // Load signals, vregs, current buffers, and unpack settings of operands and masks
    FLAGS_T  [OP_CNT-1:0]                  op_load_flags;
    cfg_vsew [OP_CNT-1:0]                  op_load_eew;
    logic    [OP_CNT-1:0][MAX_VPORT_W-1:0] op_buffer;
    FLAGS_T  [OP_CNT-1:0]                  op_extract_flags;
    cfg_vsew [OP_CNT-1:0]                  op_extract_eew;
    logic    [OP_CNT-1:0][31           :0] op_xval;
    always_comb begin
        for (int i = 0; i < OP_CNT; i++) begin
            op_load_flags   [i] = stage_state[OP_STAGE[i]    ].op_flags[i];
            op_load_eew     [i] = stage_state[OP_STAGE[i]    ].eew;
            op_buffer       [i] = stage_state[OP_STAGE[i] + 1].op_buffer[i];
            op_extract_flags[i] = stage_state[OP_STAGE[i] + 1].op_flags[i];
            op_extract_eew  [i] = stage_state[OP_STAGE[i] + 1].eew;
            op_xval         [i] = stage_state[OP_STAGE[i] + 1].op_xval[i];
        end
    end

    // Operand buffer update logic
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            logic [OP_W[i]-1:0] op_default;
            // move next mask section (depends on EEW) into lower 3/4 of operand part for masks
            if (OP_MASK[i]) begin
                if (OP_ALWAYS_ELEMWISE[i]) begin
                    if (OP_W[i] > 1) begin
                        assign op_default[OP_W[i]-2:0] = op_buffer[i][OP_W[i]-1:1];
                    end else begin
                        assign op_default = DONT_CARE_ZERO ? '0 : 'x;
                    end
                end else begin
                    always_comb begin
                        op_default = op_buffer[i][OP_W[i]-1:0];
                        op_default[(OP_W[i]*3)/4-1:0] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case (op_load_eew[i])
                            VSEW_16: op_default[(OP_W[i]*3)/4-1:0        ] =
                                   op_buffer[i][(OP_W[i]*5)/4-1:OP_W[i]/2];
                            VSEW_32: op_default[(OP_W[i]*3)/4-1:0        ] =
                                   op_buffer[i][ OP_W[i]     -1:OP_W[i]/4];
                            default: ;
                        endcase
                        if (OP_ALLOW_ELEMWISE[i] & op_load_flags[i].elemwise) begin
                            op_default[OP_W[i]-2:0] = op_buffer[i][OP_W[i]-1:1];
                        end
                    end
                end
            end
            // shift down operand part by one byte, halfword, or word for element-wise unpacking
            else if (OP_ALWAYS_ELEMWISE[i] | OP_ALLOW_ELEMWISE[i]) begin
                always_comb begin
                    op_default = op_buffer[i][OP_W[i]-1:0];
                    if (~OP_HOLD_FLAG[i] | ~op_load_flags[i].hold) begin
                        op_default[OP_W[i]-9:0] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case ({op_load_eew[i], OP_NARROW[i] & op_load_flags[i].narrow})
                            {VSEW_8 , 1'b0},
                            {VSEW_16, 1'b1}: op_default[OP_W[i]-9:0] = op_buffer[i][OP_W[i]-1 :8 ];
                            {VSEW_16, 1'b0},
                            {VSEW_32, 1'b1}: op_default[OP_W[i]-9:0] = op_buffer[i][OP_W[i]+7 :16];
                            {VSEW_32, 1'b0}: op_default[OP_W[i]-9:0] = op_buffer[i][OP_W[i]+23:32];
                            default: ;
                        endcase
                    end
                end
            end
            // shift down upper half of operand part to support narrow operands
            else if (OP_NARROW[i]) begin
                always_comb begin
                    op_default = op_buffer[i][OP_W[i]-1:0];
                    if (~OP_HOLD_FLAG[i] | ~op_load_flags[i].hold) begin
                        op_default[OP_W[i]/2-1:0] = op_buffer[i][OP_W[i]-1:OP_W[i]/2];
                    end
                end
            end
            // retain current value if nothing was selected
            else begin
                assign op_default = op_buffer[i][OP_W[i]-1:0];
            end

            always_comb begin
                // by default, retain current value for upper part and assign default value for
                // lower part
                op_buffer_next[i] = {op_buffer[i][MAX_VPORT_W-1:OP_W[i]], op_default};
                // shift signal overrides mask, narrow, or element-wise updates and shifts entire
                // content right by the width of the operand; full-size operands shift every cycle
                if ((~OP_MASK[i] & ~OP_NARROW[i] & ~OP_ALLOW_ELEMWISE[i] & ~OP_ALWAYS_ELEMWISE[i]) |
                    op_load_flags[i].shift
                ) begin
                    op_buffer_next[i][VPORT_W[OP_SRC[i]]-OP_W[i]-1:0      ] =
                         op_buffer[i][VPORT_W[OP_SRC[i]]        -1:OP_W[i]];
                end
                // load signal overrides all others and moves vreg value into buffer
                if (op_load_flags[i].load) begin
                    op_buffer_next[i][VPORT_W[OP_SRC[i]]-1:0] =
                      op_vreg_data[i][VPORT_W[OP_SRC[i]]-1:0];
                end
            end
        end
    endgenerate

    // Operand extraction logic
    generate
        for (genvar i = 0; i < OP_CNT; i++) begin
            always_comb begin
                // operand is lower part of operand buffer by default
                op_data[i]              = DONT_CARE_ZERO ? '0 : 'x;
                op_data[i][OP_W[i]-1:0] = op_buffer[i][OP_W[i]-1:0];
                if (OP_MASK[i]) begin
                    if (OP_ALWAYS_ELEMWISE[i]) begin
                        // An always element-wise mask consists of only one bit, however all the
                        // lower OP_W bits of the buffer are moved to the operand without
                        // modification (which is the default for full-size operands) to support
                        // alternative uses of the mask data in the first cycle of an instruction.
                    end else begin
                        // convert element mask to byte mask if this operand is a mask
                        op_data[i][OP_W[i]-1:0] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case (op_extract_eew[i])
                            VSEW_8: begin
                                op_data[i][OP_W[i]-1:0] = op_buffer[i][OP_W[i]-1:0];
                            end
                            VSEW_16: begin
                                for (int j = 0; j < OP_W[i] / 2; j++) begin
                                    op_data[i][j*2  ] = op_buffer[i][j];
                                    op_data[i][j*2+1] = op_buffer[i][j];
                                end
                            end
                            VSEW_32: begin
                                for (int j = 0; j < OP_W[i] / 4; j++) begin
                                    op_data[i][j*4  ] = op_buffer[i][j];
                                    op_data[i][j*4+1] = op_buffer[i][j];
                                    op_data[i][j*4+2] = op_buffer[i][j];
                                    op_data[i][j*4+3] = op_buffer[i][j];
                                end
                            end
                            default: ;
                        endcase
                    end
                end else begin
                    // extend each element to twice its size if this operand is narrow
                    if (OP_NARROW[i] & op_extract_flags[i].narrow) begin
                        op_data[i] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case (op_extract_eew[i])
                            VSEW_16: begin
                                for (int j = 0; j < OP_W[i] / 16; j++) begin
                                    op_data[i][16*j +: 16] = {
                                        // upper bits are either sign or zero extended
                                        {8 {op_extract_flags[i].sigext & op_buffer[i][8 *j + 7 ]}},
                                        op_buffer[i][8 *j +: 8 ]
                                    };
                                end
                            end
                            VSEW_32: begin
                                for (int j = 0; j < OP_W[i] / 32; j++) begin
                                    op_data[i][32*j +: 32] = {
                                        // upper bits are either sign or zero extended
                                        {16{op_extract_flags[i].sigext & op_buffer[i][16*j + 15]}},
                                        op_buffer[i][16*j +: 16]
                                    };
                                end
                            end
                            default: ;
                        endcase
                    end
                    // fill operand elements with lower bits of XREG value if this operand is no vreg
                    if (OP_XREG[i] & ~op_extract_flags[i].vreg) begin
                        op_data[i] = DONT_CARE_ZERO ? '0 : 'x;
                        unique case (op_extract_eew[i])
                            VSEW_8: begin
                                for (int j = 0; j < OP_W[i] / 8; j++) begin
                                    op_data[i][8*j  +: 8 ] = op_xval[i][7 :0];
                                end
                            end
                            VSEW_16: begin
                                for (int j = 0; j < OP_W[i] / 16; j++) begin
                                    op_data[i][16*j +: 16] = op_xval[i][15:0];
                                end
                            end
                            VSEW_32: begin
                                for (int j = 0; j < OP_W[i] / 32; j++) begin
                                    op_data[i][32*j +: 32] = op_xval[i];
                                end
                            end
                            default: ;
                        endcase
                    end
                end
            end
        end
    endgenerate

    // Collect load signals and vreg addresses of valid stages up to load stage of the respective
    // operand and combine them into a pending read mask
    logic [UNPACK_STAGES:0][VPORT_CNT-1:0][(1<<MAX_VADDR_W)-1:0] pend_vreg_reads;
    generate
        for (genvar i = 0; i < UNPACK_STAGES + 1; i++) begin
            for (genvar j = 0; j < VPORT_CNT; j++) begin
                always_comb begin
                    pend_vreg_reads[i][j] = '0;
                    for (int k = 0; k < OP_CNT; k++) begin
                        if ((j == OP_SRC[k]) & (i <= OP_STAGE[k]) & ~OP_ADDR_OFFSET_OP0[k]) begin
                            if (stage_valid[i] & stage_state[i].op_flags[k].load & (
                                ~OP_XREG[k]    | stage_state[i].op_flags[k].vreg)
                            ) begin
                                if (VPORT_ADDR_ZERO[j]) begin
                                    pend_vreg_reads[i][j][0   +: (1 << (MAX_VADDR_W-VADDR_W[j]))
                                    ] = '1;
                                end else begin
                                    pend_vreg_reads[i][j][
                                        (stage_state[i].op_vaddr[k] << (MAX_VADDR_W-VADDR_W[j])) +:
                                                                 (1 << (MAX_VADDR_W-VADDR_W[j]))
                                    ] = '1;
                                end
                            end
                        end
                    end
                end
            end
        end
    endgenerate
    always_comb begin
        pending_vreg_reads_o = '0;
        for (int i = 0; i < UNPACK_STAGES + 1; i++) begin
            for (int j = 0; j < VPORT_CNT; j++) begin
                pending_vreg_reads_o |= pend_vreg_reads[i][j];
            end
        end
    end

    // Stage valid and control signals flags.  These flags allow to check whether any of the unpack
    // stages is valid and to check whether a flag that is part of the control signals is set in any
    // or in all valid stages.
    always_comb begin
        stage_valid_any_o = stage_valid != '0;
        ctrl_flags_any_o  = {CTRL_DATA_W{1'b0}};
        ctrl_flags_all_o  = {CTRL_DATA_W{1'b1}};
        for (int i = 0; i < UNPACK_STAGES + 1; i++) begin
            if (stage_valid[i]) begin
                ctrl_flags_any_o |= stage_state[i].ctrl;
                ctrl_flags_all_o &= stage_state[i].ctrl;
            end
        end
    end


`ifdef VPROC_SVA
`include "vproc_vregunpack_sva.svh"
`endif

endmodule
