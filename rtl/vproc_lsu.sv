// Copyright TU Wien
// Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


module vproc_lsu #(
        parameter int unsigned        VMEM_W          = 32,   // width in bits of the vector memory interface
        parameter bit                 BUF_REQUEST     = 1'b1, // insert pipeline stage before issuing request
        parameter bit                 BUF_RDATA       = 1'b1, // insert pipeline stage after memory read
        parameter type                CTRL_T          = logic,
        parameter int unsigned        XIF_ID_W        = 3,    // width in bits of instruction IDs
        parameter int unsigned        XIF_ID_CNT      = 8,    // total count of instruction IDs
        parameter bit                 ADDR_ALIGNED    = 1'b1, // base address is aligned to VMEM_W
        parameter bit                 DONT_CARE_ZERO  = 1'b0  // initialize don't care values to zero
    )
    (
        input  logic                  clk_i,
        input  logic                  async_rst_ni,
        input  logic                  sync_rst_ni,

        input  logic                  pipe_in_valid_i,
        output logic                  pipe_in_ready_o,
        input  CTRL_T                 pipe_in_ctrl_i,
        input  logic [31          :0] pipe_in_op1_i,
        input  logic [VMEM_W    -1:0] pipe_in_op2_i,
        input  logic [VMEM_W/8  -1:0] pipe_in_mask_i,

        output logic                  pipe_out_valid_o,
        input  logic                  pipe_out_ready_i,
        output CTRL_T                 pipe_out_ctrl_o,
        output logic                  pipe_out_pend_clr_o,
        output logic [VMEM_W    -1:0] pipe_out_res_o,
        output logic [VMEM_W/8  -1:0] pipe_out_mask_o,

        output logic                  pending_load_o,
        output logic                  pending_store_o,

        input  logic [31:0]           vreg_pend_rd_i,

        input  logic [XIF_ID_CNT-1:0] instr_spec_i,
        input  logic [XIF_ID_CNT-1:0] instr_killed_i,
        output logic                  instr_done_valid_o,
        output logic [XIF_ID_W-1:0]   instr_done_id_o,

        output logic                  trans_complete_valid_o,
        output logic [XIF_ID_W-1:0]   trans_complete_id_o,
        output logic                  trans_complete_exc_o,
        output logic [5:0]            trans_complete_exccode_o,

        vproc_xif.coproc_mem          xif_mem_if,
        vproc_xif.coproc_mem_result   xif_memres_if
    );

    import vproc_pkg::*;

    // reduced LSU state for passing through the queue
    typedef struct packed {
        logic                        first_cycle;
        logic                        last_cycle;
        logic [XIF_ID_W-1:0]         id;
        op_mode_lsu                  mode;
        logic [$clog2(VMEM_W/8)-1:0] vl_part;
        logic                        vl_part_0;
        logic [4:0]                  res_vaddr;
        logic                        res_store;
        logic                        res_shift;
        logic                        exc;
        logic [5:0]                  exccode;
    } lsu_state_red;

    logic mem_result_valid; // XIF mem_result_valid guarded by LSU queue deq_valid_o


    ///////////////////////////////////////////////////////////////////////////
    // LSU BUFFERS

    logic         state_req_ready,   lsu_queue_ready;
    logic         state_req_stall;
    logic         state_req_valid_q, state_req_valid_d, state_rdata_valid_q;
    CTRL_T        state_req_q,       state_req_d;
    lsu_state_red                                       state_rdata_q,       state_rdata_d;

    assign pending_load_o  = state_req_valid_q & ~state_req_q.mode.lsu.store;
    assign pending_store_o = state_req_valid_q &  state_req_q.mode.lsu.store;

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
                    state_rdata_valid_q <= mem_result_valid & ~state_rdata_d.mode.store;
                end
            end
            always_ff @(posedge clk_i) begin : vproc_lsu_stage_rdata
                if (mem_result_valid) begin
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
                state_rdata_valid_q = mem_result_valid & ~state_rdata_d.mode.store;
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

    // Stall vreg writes until pending reads of the destination register are
    // complete and while the instruction is speculative; for the LSU stalling
    // has to happen at the request stage, since later stalling is not possible
    assign state_req_stall = (~state_req_q.mode.lsu.store & state_req_q.res_store & vreg_pend_rd_i[state_req_q.res_vaddr]) | instr_spec_i[state_req_q.id] | ~lsu_queue_ready;

    assign instr_done_valid_o = state_req_valid_q & state_req_q.last_cycle & xif_mem_if.mem_valid & xif_mem_if.mem_ready;
    assign instr_done_id_o    = state_req_q.id;


    ///////////////////////////////////////////////////////////////////////////
    // LSU READ/WRITE

    assign state_req_valid_d = pipe_in_valid_i;
    assign state_req_d       = pipe_in_ctrl_i;
    assign pipe_in_ready_o   = state_req_ready;

    logic [31        :0] vs2_data;
    logic [VMEM_W  -1:0] vs3_data;
    logic [VMEM_W/8-1:0] vmsk_data;
    assign vs2_data  = pipe_in_op1_i;
    assign vs3_data  = pipe_in_op2_i;
    assign vmsk_data = pipe_in_mask_i;

    // compose memory address:
    always_comb begin
        req_addr_d = DONT_CARE_ZERO ? '0 : 'x;
        unique case (pipe_in_ctrl_i.mode.lsu.stride)
            // For (unit-)strided memory requests, the address is initialized with the X register
            // value during the first cycle and incremented during later cycles, but it is left
            // unchanged in case the input is invalid (avoids corrupting the address).  Note that
            // for strided loads, the X register value holds the base address in the first cycle
            // and then switches to the increment value.
            LSU_UNITSTRIDE: req_addr_d = pipe_in_valid_i ? (pipe_in_ctrl_i.first_cycle ?
                pipe_in_ctrl_i.xval : req_addr_q + 32'(VMEM_W / 8)
            ) : req_addr_q;
            LSU_STRIDED:    req_addr_d = pipe_in_valid_i ? (pipe_in_ctrl_i.first_cycle ?
                pipe_in_ctrl_i.xval : req_addr_q + pipe_in_ctrl_i.xval
            ) : req_addr_q;
            LSU_INDEXED: begin
                unique case (pipe_in_ctrl_i.mode.lsu.eew)
                    VSEW_8:  req_addr_d = pipe_in_ctrl_i.xval + {24'b0, vs2_data[7 :0]};
                    VSEW_16: req_addr_d = pipe_in_ctrl_i.xval + {16'b0, vs2_data[15:0]};
                    VSEW_32: req_addr_d = pipe_in_ctrl_i.xval +         vs2_data[31:0] ;
                    default: ;
                endcase
            end
            default: ;
        endcase
    end

    assign vmsk_tmp_d = vmsk_data;

    // write data conversion and masking:
    logic [VMEM_W/8-1:0] wdata_unit_vl_mask;
    logic                wdata_stri_mask;
    assign wdata_unit_vl_mask = ~pipe_in_ctrl_i.vl_part_0 ? ({(VMEM_W/8){1'b1}} >> (~pipe_in_ctrl_i.vl_part)) : '0;
    assign wdata_stri_mask    = ~pipe_in_ctrl_i.vl_part_0 &
                                (pipe_in_ctrl_i.mode.lsu.masked ? vmsk_data[0] : 1'b1);
    always_comb begin
        wdata_buf_d = DONT_CARE_ZERO ? '0 : 'x;
        wmask_buf_d = DONT_CARE_ZERO ? '0 : 'x;
        if (pipe_in_ctrl_i.mode.lsu.stride == LSU_UNITSTRIDE) begin
            wdata_buf_d = vs3_data[VMEM_W-1:0];
            wmask_buf_d = (pipe_in_ctrl_i.mode.lsu.masked ? vmsk_data : '1) & wdata_unit_vl_mask;
        end else begin
            unique case (pipe_in_ctrl_i.mode.lsu.eew)
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
            if (~ADDR_ALIGNED) begin
                wdata_buf_d = vs3_data[VMEM_W-1:0];
                unique case (pipe_in_ctrl_i.mode.lsu.eew)
                    VSEW_8:  wmask_buf_d = {{VMEM_W/8-1{1'b0}},    wdata_stri_mask  };
                    VSEW_16: wmask_buf_d = {{VMEM_W/8-2{1'b0}}, {2{wdata_stri_mask}}};
                    VSEW_32: wmask_buf_d = {{VMEM_W/8-4{1'b0}}, {4{wdata_stri_mask}}};
                    default: ;
                endcase
            end
        end
    end

    // memory request (keep requesting next access while addressing is not complete)
    assign xif_mem_if.mem_valid     = state_req_valid_q & ~state_req_stall & ~instr_killed_i[state_req_q.id] & (~mem_exc_q | state_req_q.first_cycle);
    assign xif_mem_if.mem_req.id    = state_req_q.id;
    assign xif_mem_if.mem_req.addr  = ADDR_ALIGNED ? {req_addr_q[31:$clog2(VMEM_W/8)], {$clog2(VMEM_W/8){1'b0}}} : req_addr_q;
    assign xif_mem_if.mem_req.mode  = '0;
    assign xif_mem_if.mem_req.we    = state_req_q.mode.lsu.store;
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
        state_req_red.first_cycle = state_req_q.first_cycle;
        state_req_red.last_cycle  = state_req_q.last_cycle;
        state_req_red.id          = state_req_q.id;
        state_req_red.mode        = state_req_q.mode.lsu;
        state_req_red.vl_part     = state_req_q.vl_part;
        state_req_red.vl_part_0   = state_req_q.vl_part_0;
        state_req_red.res_vaddr   = state_req_q.res_vaddr;
        state_req_red.res_store   = state_req_q.res_store;
        state_req_red.res_shift   = state_req_q.res_shift;
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
        .deq_ready_i  ( mem_result_valid | mem_err_d                                  ),
        .deq_valid_o  ( deq_valid                                                     ),
        .deq_data_o   ( {rdata_off_d, rmask_buf_d, deq_state}                         ),
        .flags_any_o  (                                                               ),
        .flags_all_o  (                                                               )
    );
    assign mem_result_valid = xif_memres_if.mem_result_valid & deq_valid;

    // monitor the memory result for bus errors and the queue for exceptions
    always_comb begin
        mem_err_d     = mem_err_q;
        mem_exccode_d = mem_exccode_q;
        if ((deq_valid & deq_state.first_cycle) | ~mem_err_q) begin
            // reset the error flag in the first cycle, unless there is a bus
            // error or an exception occured during the request
            mem_err_d     = deq_state.exc | (mem_result_valid & xif_memres_if.mem_result.err);
            mem_exccode_d = deq_state.exc ? deq_state.exccode : (
                // bus error translates to a load/store access fault exception
                deq_state.mode.store ? 6'h07 : 6'h05
            );
        end
    end

    // LSU result (indicates potential exceptions):
    assign trans_complete_valid_o   = deq_valid & deq_state.last_cycle & (mem_result_valid | mem_err_d);
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
    logic [VMEM_W/8-1:0] rdata_unit_vl_mask, rdata_unit_vdmsk;
    logic rdata_stri_vdmsk;
    assign rdata_unit_vl_mask = ~state_rdata_q.vl_part_0 ? ({(VMEM_W/8){1'b1}} >> (~state_rdata_q.vl_part)) : '0;
    assign rdata_unit_vdmsk   = (state_rdata_q.mode.masked ? rmask_buf_q : {VMEM_W/8{1'b1}}) & rdata_unit_vl_mask;
    assign rdata_stri_vdmsk   = ~state_rdata_q.vl_part_0 & (state_rdata_q.mode.masked ? rmask_buf_q[0] : 1'b1);

    assign pipe_out_valid_o = state_rdata_valid_q;
    always_comb begin
        pipe_out_ctrl_o              = DONT_CARE_ZERO ? '0 : 'x;
        pipe_out_ctrl_o.first_cycle  = state_rdata_q.first_cycle;
        pipe_out_ctrl_o.last_cycle   = state_rdata_q.last_cycle;
        pipe_out_ctrl_o.id           = state_rdata_q.id;
        pipe_out_ctrl_o.mode.lsu     = state_rdata_q.mode;
        pipe_out_ctrl_o.eew          = state_rdata_q.mode.eew;
        pipe_out_ctrl_o.vl_part      = state_rdata_q.vl_part;
        pipe_out_ctrl_o.vl_part_0    = state_rdata_q.vl_part_0;
        pipe_out_ctrl_o.res_vaddr    = state_rdata_q.res_vaddr;
        pipe_out_ctrl_o.res_store    = state_rdata_q.res_store & ~state_rdata_q.exc;
        pipe_out_ctrl_o.res_shift    = state_rdata_q.res_shift;
    end
    assign pipe_out_pend_clr_o = state_rdata_q.res_store;
    always_comb begin
        if (state_rdata_q.mode.stride == LSU_UNITSTRIDE) begin
            pipe_out_res_o = rdata_buf_q;
        end else begin
            pipe_out_res_o = DONT_CARE_ZERO ? '0 : 'x;
            unique case (state_rdata_q.mode.eew)
                VSEW_8:  pipe_out_res_o[7 :0] = rdata_buf_q[{3'b000, rdata_off_q                                  } * 8 +: 8 ];
                VSEW_16: pipe_out_res_o[15:0] = rdata_buf_q[{3'b000, rdata_off_q & ({$clog2(VMEM_W/8){1'b1}} << 1)} * 8 +: 16];
                VSEW_32: pipe_out_res_o[31:0] = rdata_buf_q[{3'b000, rdata_off_q & ({$clog2(VMEM_W/8){1'b1}} << 2)} * 8 +: 32];
                default: ;
            endcase
            if (~ADDR_ALIGNED) begin
                pipe_out_res_o = rdata_buf_q;
            end
        end
        pipe_out_mask_o = (state_rdata_q.mode.stride == LSU_UNITSTRIDE) ? rdata_unit_vdmsk : {(VMEM_W/8){rdata_stri_vdmsk}};
    end


endmodule
