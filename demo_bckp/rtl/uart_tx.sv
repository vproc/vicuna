/*
 The MIT License (MIT)

 Copyright (c) 2019 Yuya Kudo.

 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in
 all copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 THE SOFTWARE.
*/


module uart_tx #(
        parameter DATA_WIDTH = 8,
        parameter BAUD_RATE  = 115200,
        parameter CLK_FREQ   = 100_000_000
    )
    (
        input  logic                  clk_i,
        input  logic                  rst_ni,

        input  logic                  valid_i,
        input  logic [DATA_WIDTH-1:0] data_i,
        output logic                  ready_o,
        output logic                  tx_o
    );

    localparam LB_DATA_WIDTH    = $clog2(DATA_WIDTH);
    localparam PULSE_WIDTH      = CLK_FREQ / BAUD_RATE;
    localparam LB_PULSE_WIDTH   = $clog2(PULSE_WIDTH);
    localparam HALF_PULSE_WIDTH = PULSE_WIDTH / 2;

    typedef enum logic [1:0] {STT_DATA,
                              STT_STOP,
                              STT_WAIT
                              } statetype;

    statetype                 state;

    logic [DATA_WIDTH-1:0]     data_r;
    logic                      sig_r;
    logic                      ready_r;
    logic [LB_DATA_WIDTH-1:0]  data_cnt;
    logic [LB_PULSE_WIDTH:0]   clk_cnt;

    always_ff @(posedge clk_i) begin
       if(!rst_ni) begin
          state    <= STT_WAIT;
          sig_r    <= 1;
          data_r   <= 0;
          ready_r  <= 1;
          data_cnt <= 0;
          clk_cnt  <= 0;
       end
       else begin

          //-----------------------------------------------------------------------------
          // 3-state FSM
          case(state)

            //-----------------------------------------------------------------------------
            // state      : STT_DATA
            // behavior   : serialize and transmit data
            // next state : when all data have transmited -> STT_STOP
            STT_DATA: begin
               if(0 < clk_cnt) begin
                  clk_cnt <= clk_cnt - 1;
               end
               else begin
                  sig_r   <= data_r[data_cnt];
                  clk_cnt <= PULSE_WIDTH;

                  if(data_cnt == DATA_WIDTH - 1) begin
                     state <= STT_STOP;
                  end
                  else begin
                     data_cnt <= data_cnt + 1;
                  end
               end
            end

            //-----------------------------------------------------------------------------
            // state      : STT_STOP
            // behavior   : assert stop bit
            // next state : STT_WAIT
            STT_STOP: begin
               if(0 < clk_cnt) begin
                  clk_cnt <= clk_cnt - 1;
               end
               else begin
                  state   <= STT_WAIT;
                  sig_r   <= 1;
                  clk_cnt <= PULSE_WIDTH + HALF_PULSE_WIDTH;
               end
            end

            //-----------------------------------------------------------------------------
            // state      : STT_WAIT
            // behavior   : watch valid signal, and assert start bit when valid signal assert
            // next state : when valid signal assert -> STT_STAT
            STT_WAIT: begin
               if(0 < clk_cnt) begin
                  clk_cnt <= clk_cnt - 1;
               end
               else if(!ready_r) begin
                  ready_r <= 1;
               end
               else if(valid_i) begin
                  state    <= STT_DATA;
                  sig_r    <= 0;
                  data_r   <= data_i;
                  ready_r  <= 0;
                  data_cnt <= 0;
                  clk_cnt  <= PULSE_WIDTH;
               end
            end

            default: begin
               state <= STT_WAIT;
            end
          endcase
       end
    end

    assign tx_o    = sig_r;
    assign ready_o = ready_r;

endmodule
