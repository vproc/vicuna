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


module uart_rx #(
        parameter DATA_WIDTH = 8,
        parameter BAUD_RATE  = 115200,
        parameter CLK_FREQ   = 100_000_000
    )
    (
        input  logic                  clk_i,
        input  logic                  rst_ni,

        input  logic                  rx_i,
        input  logic                  ready_i,
        output logic                  valid_o,
        output logic [DATA_WIDTH-1:0] data_o
    );

    localparam LB_DATA_WIDTH    = $clog2(DATA_WIDTH);
    localparam PULSE_WIDTH      = CLK_FREQ / BAUD_RATE;
    localparam LB_PULSE_WIDTH   = $clog2(PULSE_WIDTH);
    localparam HALF_PULSE_WIDTH = PULSE_WIDTH / 2;

    //-----------------------------------------------------------------------------
    // noise removing filter
    function majority5(input [4:0] val);
       case(val)
         5'b00000: majority5 = 0;
         5'b00001: majority5 = 0;
         5'b00010: majority5 = 0;
         5'b00100: majority5 = 0;
         5'b01000: majority5 = 0;
         5'b10000: majority5 = 0;
         5'b00011: majority5 = 0;
         5'b00101: majority5 = 0;
         5'b01001: majority5 = 0;
         5'b10001: majority5 = 0;
         5'b00110: majority5 = 0;
         5'b01010: majority5 = 0;
         5'b10010: majority5 = 0;
         5'b01100: majority5 = 0;
         5'b10100: majority5 = 0;
         5'b11000: majority5 = 0;
         default:  majority5 = 1;
       endcase
    endfunction

    //-----------------------------------------------------------------------------
    // description about input signal
    logic [1:0] sampling_cnt;
    logic [4:0] sig_q;
    logic       sig_r;

    always_ff @(posedge clk_i) begin
       if(!rst_ni) begin
          sampling_cnt <= 0;
          sig_q        <= 5'b11111;
          sig_r        <= 1;
       end
       else begin
          // connect to deserializer after removing noise
          if(sampling_cnt == 0) begin
             sig_q <= {rx_i, sig_q[4:1]};
          end

          sig_r        <= majority5(sig_q);
          sampling_cnt <= sampling_cnt + 1;
       end
    end

    //----------------------------------------------------------------
    // description about receive UART signal
    typedef enum logic [1:0] {STT_DATA,
                              STT_STOP,
                              STT_WAIT
                              } statetype;

    statetype                 state;

    logic [DATA_WIDTH-1:0]   data_tmp_r;
    logic [LB_DATA_WIDTH:0]  data_cnt;
    logic [LB_PULSE_WIDTH:0] clk_cnt;
    logic                    rx_done;

    always_ff @(posedge clk_i) begin
       if(!rst_ni) begin
          state      <= STT_WAIT;
          data_tmp_r <= 0;
          data_cnt   <= 0;
          clk_cnt    <= 0;
       end
       else begin

          //-----------------------------------------------------------------------------
          // 3-state FSM
          case(state)

            //-----------------------------------------------------------------------------
            // state      : STT_DATA
            // behavior   : deserialize and recieve data
            // next state : when all data have recieved -> STT_STOP
            STT_DATA: begin
               if(0 < clk_cnt) begin
                  clk_cnt <= clk_cnt - 1;
               end
               else begin
                  data_tmp_r <= {sig_r, data_tmp_r[DATA_WIDTH-1:1]};
                  clk_cnt    <= PULSE_WIDTH;

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
            // behavior   : watch stop bit
            // next state : STT_WAIT
            STT_STOP: begin
               if(0 < clk_cnt) begin
                  clk_cnt <= clk_cnt - 1;
               end
               else if(sig_r) begin
                  state <= STT_WAIT;
               end
            end

            //-----------------------------------------------------------------------------
            // state      : STT_WAIT
            // behavior   : watch start bit
            // next state : when start bit is observed -> STT_DATA
            STT_WAIT: begin
               if(sig_r == 0) begin
                  clk_cnt  <= PULSE_WIDTH + HALF_PULSE_WIDTH;
                  data_cnt <= 0;
                  state    <= STT_DATA;
               end
            end

            default: begin
               state <= STT_WAIT;
            end
          endcase
       end
    end

    assign rx_done = (state == STT_STOP) && (clk_cnt == 0);

    //-----------------------------------------------------------------------------
    // description about output signal
    logic [DATA_WIDTH-1:0] data_r;
    logic                  valid_r;

    always_ff @(posedge clk_i) begin
       if(!rst_ni) begin
          data_r  <= 0;
          valid_r <= 0;
       end
       else if(rx_done && !valid_r) begin
          valid_r <= 1;
          data_r  <= data_tmp_r;
       end
       else if(valid_r && ready_i) begin
          valid_r <= 0;
       end
    end

    assign data_o  = data_r;
    assign valid_o = valid_r;

endmodule
