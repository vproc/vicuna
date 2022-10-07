// TODO DO THIS

module vproc_div #(
        parameter vproc_pkg::div_type DIV_TYPE     = vproc_pkg::DIV_GENERIC,
        parameter bit                 BUF_OPERANDS = 1'b1,
        parameter bit                 BUF_DIV_IN   = 1'b1,
        parameter bit                 BUF_DIV_OUT  = 1'b1,
        parameter bit                 BUF_RESULTS  = 1'b1
        // parameter bit                 DONT_CARE_ZERO = 1'b0
    )(
        input  logic                  clk_i,
        input  logic                  async_rst_ni,
        input  logic                  sync_rst_ni,

        input  logic                  pipe_in_valid_i,
        output logic                  pipe_in_ready_o,
        
        output logic                  pipe_out_valid_o,
        input  logic                  pipe_out_ready_i
    );

    import vproc_pkg::*;

endmodule

