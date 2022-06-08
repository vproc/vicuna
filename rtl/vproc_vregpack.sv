// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


// Packing results into vector registers
module vproc_vregpack #(
        // vector register port configuration
        parameter int unsigned                      VPORT_W             = 0,    // vreg port width
        parameter int unsigned                      VADDR_W             = 5,    // vreg address width
        parameter int unsigned                      VPORT_WR_ATTEMPTS   = 1,    // number of write attempts
        parameter bit                               VPORT_PEND_CLR_BULK = '0,   // clear pending wr in bulk

        // vector register result configuration
        parameter int unsigned                      MAX_RES_W           = 64,
        parameter int unsigned                      RES_CNT             = 1,
        parameter int unsigned                      RES_W[RES_CNT]      = '{0}, // result width
        parameter bit [RES_CNT-1:0]                 RES_MASK            = '0,   // result is a mask
        parameter bit [RES_CNT-1:0]                 RES_NARROW          = '0,   // result may be narrow
        parameter bit [RES_CNT-1:0]                 RES_ALLOW_ELEMWISE  = '0,   // result may be 1 elem
        parameter bit [RES_CNT-1:0]                 RES_ALWAYS_ELEMWISE = '0,   // result is 1 elem

        parameter type                              FLAGS_T             = logic,// flags struct type
        parameter int unsigned                      INSTR_ID_W          = 3,    // instruction IDs width
        parameter int unsigned                      INSTR_ID_CNT        = 8,    // number of instr IDs
        parameter bit                               DONT_CARE_ZERO      = 1'b0  // set don't care 0
    )(
        input  logic                                clk_i,
        input  logic                                async_rst_ni,
        input  logic                                sync_rst_ni,

        // pipeline in
        input  logic                                pipe_in_valid_i,
        output logic                                pipe_in_ready_o,
        input  logic   [INSTR_ID_W            -1:0] pipe_in_instr_id_i,     // ID of instruction
        input  vproc_pkg::cfg_vsew                  pipe_in_eew_i,          // current elem width
        input  logic   [VADDR_W               -1:0] pipe_in_vaddr_i,        // vreg address
        input  logic   [RES_CNT-1:0]                pipe_in_res_store_i,    // result store signal
        input  logic   [RES_CNT-1:0]                pipe_in_res_valid_i,    // result is valid
        input  FLAGS_T [RES_CNT-1:0]                pipe_in_res_flags_i,    // result flags
        input  logic   [RES_CNT-1:0][MAX_RES_W-1:0] pipe_in_res_data_i,     // result data
        input  logic   [RES_CNT-1:0][MAX_RES_W-1:0] pipe_in_res_mask_i,     // result mask
        input  logic                                pipe_in_pend_clr_i,     // clear pend writes
        input  logic   [$clog2(VADDR_W-1)     -1:0] pipe_in_pend_clr_cnt_i, // vregs to clear count
        input  logic                                pipe_in_instr_done_i,   // instr done flag

        // vector register file write port
        output logic                                vreg_wr_valid_o,
        input  logic                                vreg_wr_ready_i,
        output logic   [VADDR_W               -1:0] vreg_wr_addr_o,         // vreg write address
        output logic   [VPORT_W/8             -1:0] vreg_wr_be_o,           // vreg byte enable
        output logic   [VPORT_W               -1:0] vreg_wr_data_o,         // vreg write data
        output logic                                vreg_wr_clr_o,          // clear addr from pend writes
        output logic   [$clog2(VADDR_W-1)     -1:0] vreg_wr_clr_cnt_o,      // number of vregs to clear

        // pending vector register reads (writes stall if the destination register is not clear)
        input  logic   [(1<<VADDR_W)          -1:0] pending_vreg_reads_i,

        // Instruction IDs speculative and killed masks (vector register writes stall while the ID
        // of the current instruction is speculative and are inhibited if it is killed)
        input  logic   [INSTR_ID_CNT          -1:0] instr_spec_i,
        input  logic   [INSTR_ID_CNT          -1:0] instr_killed_i,

        // Signals that this instruction ID is done
        output logic                                instr_done_valid_o,
        output logic   [INSTR_ID_W            -1:0] instr_done_id_o
    );

    import vproc_pkg::*;

    if (VPORT_WR_ATTEMPTS < 1 || (1 << (VPORT_WR_ATTEMPTS - 1)) > VPORT_W / MAX_RES_W) begin
        $fatal(1, "The number of write attempts VPORT_WR_ATTEMPTS must be at least 1 and ",
                  "2^(VPORT_WR_ATTEMPTS-1) must be less than or equal to the ratio of the vector ",
                  "register port width vs the result width.  ",
                  "However, VPORT_WR_ATTEMPTS is %d and that ratio is %d.",
                  VPORT_WR_ATTEMPTS, VPORT_W / MAX_RES_W);
    end

    // max number of cycles by which a write can be delayed
    localparam int unsigned MAX_WR_DELAY = (1 << (VPORT_WR_ATTEMPTS - 1)) - 1;

    // width of the pending write vreg clear counter (choosen such that it can span up to 1/4 of the
    // vector register addresses)
    localparam int unsigned PEND_CLEAR_CNT_W = $clog2(VADDR_W-1);

    typedef struct packed {
        logic   [INSTR_ID_W            -1:0] instr_id;
        cfg_vsew                             eew;
        logic   [VADDR_W               -1:0] vaddr;
        logic   [RES_CNT-1:0]                res_store;
        FLAGS_T [RES_CNT-1:0]                res_flags;
        logic   [RES_CNT-1:0][VPORT_W  -1:0] res_buffer;
        logic   [RES_CNT-1:0][VPORT_W/8-1:0] msk_buffer;
        logic                                pend_clr;
        logic   [PEND_CLEAR_CNT_W      -1:0] pend_clr_cnt;
        logic                                instr_done;
    } vregpack_state_t;

    logic            stage_valid_q, stage_valid_d;
    vregpack_state_t stage_state_q, stage_state_d;
    logic            stage_stall;
    logic            stage_ready;
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

    logic [RES_CNT-1:0][VPORT_W  -1:0] res_buffer, res_buffer_next;
    logic [RES_CNT-1:0][VPORT_W/8-1:0] msk_buffer, msk_buffer_next;
    assign res_buffer = stage_state_q.res_buffer;
    assign msk_buffer = stage_state_q.msk_buffer;
    always_comb begin
        stage_valid_d = stage_valid_q;
        stage_state_d = stage_state_q;
        if (stage_ready) begin
            stage_valid_d              = pipe_in_valid_i;
            stage_state_d.instr_id     = pipe_in_instr_id_i;
            stage_state_d.eew          = pipe_in_eew_i;
            stage_state_d.vaddr        = pipe_in_vaddr_i;
            stage_state_d.res_store    = pipe_in_res_store_i;
            stage_state_d.res_flags    = pipe_in_res_flags_i;
            stage_state_d.pend_clr     = pipe_in_pend_clr_i;
            stage_state_d.pend_clr_cnt = pipe_in_pend_clr_cnt_i;
            stage_state_d.instr_done   = pipe_in_instr_done_i;
            for (int i = 0; i < RES_CNT; i++) begin
                if (pipe_in_res_valid_i[i]) begin
                    stage_state_d.res_buffer[i] = res_buffer_next[i];
                    stage_state_d.msk_buffer[i] = msk_buffer_next[i];
                end
            end
        end
    end

    assign stage_stall = (stage_state_q.res_store != '0) & (
        pending_vreg_reads_i[stage_state_q.vaddr] | instr_spec_i[stage_state_q.instr_id]
    );
    assign stage_ready = ~stage_valid_q | (
        ((stage_state_q.res_store == '0) | vreg_wr_ready_i) & ~stage_stall
    );

    assign pipe_in_ready_o = stage_ready;

    assign instr_done_valid_o = stage_valid_q & stage_state_q.instr_done & ~stage_stall;
    assign instr_done_id_o    = stage_state_q.instr_id;

    always_comb begin
        vreg_wr_valid_o = '0;
        vreg_wr_data_o  = DONT_CARE_ZERO ? '0 : 'x;
        vreg_wr_be_o    = DONT_CARE_ZERO ? '0 : 'x;
        for (int i = 0; i < RES_CNT; i++) begin
            if (stage_state_q.res_store[i]) begin
                vreg_wr_valid_o = stage_valid_q & ~stage_stall & ~instr_killed_i[stage_state_q.instr_id];
                vreg_wr_data_o  = RES_MASK[i] ? {8{res_buffer[i][VPORT_W/8-1:0]}} : res_buffer[i];
                vreg_wr_be_o    = msk_buffer[i];
            end
        end
    end
    assign vreg_wr_addr_o    = stage_state_q.vaddr;
    assign vreg_wr_clr_o     = stage_valid_q & stage_state_q.pend_clr & ~stage_stall;
    assign vreg_wr_clr_cnt_o = stage_state_q.pend_clr_cnt;

    logic [RES_CNT-1:0] res_saturated;
    generate
        for (genvar i = 0; i < RES_CNT; i++) begin
            if (RES_MASK[i]) begin

                // Mask destination values are always tail- and mask-agnostic (i.e., inactive
                // elements may be either left unchanged or overwritten with 1s).  Mask destination
                // values may be written at bit granularity, thus applying the undisturbed policy
                // (leaving inactive elements unchanged) would be overly complex.  Thus, inactive
                // elements are frequently overwritten with 1s in the mask packing code below.

                // Convert result byte mask to element mask and set all bits that are inactive.
                logic [RES_W[i]-1:0] res_elem;
                always_comb begin
                    res_elem = DONT_CARE_ZERO ? '0 : 'x;
                    unique case (pipe_in_eew_i)
                        VSEW_8:  for (int j = 0; j < RES_W[i]    ; j++) begin
                            res_elem[j] = pipe_in_res_data_i[i][  j] | ~pipe_in_res_mask_i[i][  j];
                        end
                        VSEW_16: for (int j = 0; j < RES_W[i] / 2; j++) begin
                            res_elem[j] = pipe_in_res_data_i[i][2*j] | ~pipe_in_res_mask_i[i][2*j];
                        end
                        VSEW_32: for (int j = 0; j < RES_W[i] / 4; j++) begin
                            res_elem[j] = pipe_in_res_data_i[i][4*j] | ~pipe_in_res_mask_i[i][4*j];
                        end
                        default: ;
                    endcase
                end
                // Shift in new mask values.  Note that for masks only the lower VPORT_W/8 bits of
                // the shift buffer are used, which corresponds to the mask for a single vector
                // register with an element width of 8 bits.  For element widths of 16 and 32 bits
                // the mask for a single vreg requires only VPORT_W/16 and VPORT_W/32 bits,
                // respectively.  For these the bits required to mask one vreg are repeated 2 and 4
                // times, respectively, to fill the lower VPORT_W/8 bits of the shift buffer.
                // Configurations where VPORT_W/16 or VPORT_W/32 are less than 8 bits require that
                // the higher parts are filled with 1s, depending on the MUL index, since in that
                // case these parts cannot be written individually.
                always_comb begin
                    res_buffer_next[i] = DONT_CARE_ZERO ? '0 : 'x;
                    unique case (pipe_in_eew_i)
                        VSEW_8: begin
                            res_buffer_next[i][0              +: VPORT_W/8 ] = {
                                res_elem,
                                res_buffer[i][ VPORT_W/8        -1 -: VPORT_W/8 -RES_W[i]  ]
                            };
                        end
                        VSEW_16: for (int j = 0; j < 2; j++) begin
                            res_buffer_next[i][(VPORT_W/16)*j +: VPORT_W/16] = {
                                res_elem[RES_W[i]/2-1:0],
                                res_buffer[i][(VPORT_W/16)*(j+1)-1 -: VPORT_W/16-RES_W[i]/2]
                            };
                            if ((VPORT_W < 128) & j[0] & ~pipe_in_res_flags_i[i].mul_idx[0]) begin
                                res_buffer_next[i][(VPORT_W/16)*j +: VPORT_W/16] = '1;
                            end
                        end
                        VSEW_32: for (int j = 0; j < 4; j++) begin
                            res_buffer_next[i][(VPORT_W/32)*j +: VPORT_W/32] = {
                                res_elem[RES_W[i]/4-1:0],
                                res_buffer[i][(VPORT_W/32)*(j+1)-1 -: VPORT_W/32-RES_W[i]/4]
                            };
                            if ((VPORT_W < 256) & j[0] & ~pipe_in_res_flags_i[i].mul_idx[0]) begin
                                res_buffer_next[i][(VPORT_W/32)*j +: VPORT_W/32] = '1;
                            end
                            if ((VPORT_W < 128) & j[1] & ~pipe_in_res_flags_i[i].mul_idx[1]) begin
                                res_buffer_next[i][(VPORT_W/32)*j +: VPORT_W/32] = '1;
                            end
                        end
                        default: ;
                    endcase
                end
                always_comb begin
                    msk_buffer_next[i] = '0;
                    unique case (pipe_in_eew_i)
                        VSEW_8:  for (int j = 0; j < (VPORT_W + 32 ) / 64 ; j++) begin
                            msk_buffer_next[i][pipe_in_res_flags_i[i].mul_idx*(VPORT_W/64 )+j] = '1;
                        end
                        VSEW_16: for (int j = 0; j < (VPORT_W + 64 ) / 128; j++) begin
                            msk_buffer_next[i][pipe_in_res_flags_i[i].mul_idx*(VPORT_W/128)+j] = '1;
                        end
                        VSEW_32: for (int j = 0; j < (VPORT_W + 128) / 256; j++) begin
                            msk_buffer_next[i][pipe_in_res_flags_i[i].mul_idx*(VPORT_W/256)+j] = '1;
                        end
                        default: ;
                    endcase
                end
                assign res_saturated[i] = '0;

            end else begin

                logic [RES_W[i]  -1:0] res_default;
                logic [RES_W[i]/8-1:0] msk_default;
                always_comb begin
                    res_default      = pipe_in_res_data_i[i][RES_W[i]  -1:0];
                    msk_default      = pipe_in_res_mask_i[i][RES_W[i]/8-1:0];
                    res_saturated[i] = '0;
                    if ((RES_ALLOW_ELEMWISE[i] & pipe_in_res_flags_i[i].elemwise) | RES_ALWAYS_ELEMWISE[i]) begin
                        res_default = DONT_CARE_ZERO ? '0 : 'x;
                        msk_default = DONT_CARE_ZERO ? '0 : 'x;
                        unique case (pipe_in_eew_i)
                            VSEW_8: begin
                                res_default = {   pipe_in_res_data_i[i][7 :0], res_buffer[i][VPORT_W  -1:VPORT_W  -RES_W[i]  +8 ]};
                                msk_default = {   pipe_in_res_mask_i[i][0]   , msk_buffer[i][VPORT_W/8-1:VPORT_W/8-RES_W[i]/8+1 ]};
                            end
                            VSEW_16: begin
                                res_default = {   pipe_in_res_data_i[i][15:0], res_buffer[i][VPORT_W  -1:VPORT_W  -RES_W[i]  +16]};
                                msk_default = {{2{pipe_in_res_mask_i[i][0]}} , msk_buffer[i][VPORT_W/8-1:VPORT_W/8-RES_W[i]/8+2 ]};
                            end
                            VSEW_32: begin
                                res_default =    {pipe_in_res_data_i[i][31:0], {RES_W[i]  -32{1'b0}}} | (res_buffer[i][VPORT_W  -1 -: RES_W[i]  ] >> 32);
                                msk_default = {{4{pipe_in_res_mask_i[i][0]}} , {RES_W[i]/8-4 {1'b0}}} | (msk_buffer[i][VPORT_W/8-1 -: RES_W[i]/8] >> 4 );
                            end
                            default: ;
                        endcase
                    end
                    else if (RES_NARROW[i] & pipe_in_res_flags_i[i].narrow) begin
                        res_default = DONT_CARE_ZERO ? '0 : 'x;
                        msk_default = DONT_CARE_ZERO ? '0 : 'x;
                        // lower half is filled with upper part of buffer
                        res_default[RES_W[i]/2 -1:0] = res_buffer[i][VPORT_W  -1 -: RES_W[i]/2 ];
                        msk_default[RES_W[i]/16-1:0] = msk_buffer[i][VPORT_W/8-1 -: RES_W[i]/16];
                        // upper half is filled with narrowed result data
                        unique case (pipe_in_eew_i)
                            VSEW_16: for (int j = 0; j < RES_W[i] / 16; j++) begin
                                res_default[RES_W[i]/2 +j*8  +: 8 ] =    pipe_in_res_data_i[i][j*16 +: 8 ];
                                msk_default[RES_W[i]/16+j         ] =    pipe_in_res_mask_i[i][j*2];
                                // saturate value
                                if (pipe_in_res_flags_i[i].saturate & (pipe_in_res_data_i[i][j*16+8  +: 8 ] != {8 {pipe_in_res_flags_i[i].sig & pipe_in_res_data_i[i][j*16+7 ]}})) begin
                                    res_default[RES_W[i]/2+j*8  +: 8 ] = pipe_in_res_flags_i[i].sig ? {pipe_in_res_data_i[i][j*16+15], {7 {~pipe_in_res_data_i[i][j*16+15]}}} : '1;
                                    res_saturated[i]                   = 1'b1;
                                end
                            end
                            VSEW_32: for (int j = 0; j < RES_W[i] / 32; j++) begin
                                res_default[RES_W[i]/2 +j*16 +: 16] =    pipe_in_res_data_i[i][j*32 +: 16];
                                msk_default[RES_W[i]/16+j*2  +: 2 ] = {2{pipe_in_res_mask_i[i][j*4]}};
                                // saturate value
                                if (pipe_in_res_flags_i[i].saturate & (pipe_in_res_data_i[i][j*32+16 +: 16] != {16{pipe_in_res_flags_i[i].sig & pipe_in_res_data_i[i][j*32+15]}})) begin
                                    res_default[RES_W[i]/2+j*16 +: 16] = pipe_in_res_flags_i[i].sig ? {pipe_in_res_data_i[i][j*32+31], {15{~pipe_in_res_data_i[i][j*32+31]}}} : '1;
                                    res_saturated[i]                   = 1'b1;
                                end
                            end
                            default: ;
                        endcase
                    end
                end
                always_comb begin
                    // by default, retain current value for lower part and assign default value for upper part
                    res_buffer_next[i] = {res_default, res_buffer[i][VPORT_W  -RES_W[i]  -1:0]};
                    msk_buffer_next[i] = {msk_default, msk_buffer[i][VPORT_W/8-RES_W[i]/8-1:0]};
                    // shift signal shifts entire content right by the width of the result; full-size results
                    // shift every cycle
                    if ((~RES_MASK[i] & ~RES_NARROW[i] & ~RES_ALLOW_ELEMWISE[i] & ~RES_ALWAYS_ELEMWISE[i]) |
                        pipe_in_res_flags_i[i].shift
                    ) begin
                        res_buffer_next[i][VPORT_W  -RES_W[i]  -1:0] = res_buffer[i][VPORT_W  -1:RES_W[i]  ];
                        msk_buffer_next[i][VPORT_W/8-RES_W[i]/8-1:0] = msk_buffer[i][VPORT_W/8-1:RES_W[i]/8];
                    end
                end

            end
        end
    endgenerate

endmodule
