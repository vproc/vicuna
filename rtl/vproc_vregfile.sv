// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC


module vproc_vregfile #(
        parameter int unsigned                   VREG_W   = 128,  // vector register width in bits
        parameter int unsigned                   PORT_W   = 128,  // port width in bits
        parameter int unsigned                   PORTS_RD = 0,    // number of read ports
        parameter int unsigned                   PORTS_WR = 0,    // number of write ports
        parameter vproc_pkg::ram_type            RAM_TYPE = vproc_pkg::RAM_GENERIC
    )(
        input  logic                             clk_i,
        input  logic                             async_rst_ni,
        input  logic                             sync_rst_ni,

        input  logic [4+$clog2(VREG_W/PORT_W):0] wr_addr_i[PORTS_WR],
        input  logic [PORT_W  -1:0]              wr_data_i[PORTS_WR],
        input  logic [PORT_W/8-1:0]              wr_be_i  [PORTS_WR],
        input  logic                             wr_we_i  [PORTS_WR],

        input  logic [4+$clog2(VREG_W/PORT_W):0] rd_addr_i[PORTS_RD],
        output logic [PORT_W-1:0]                rd_data_o[PORTS_RD]
    );

    ///////////////////////////////////////////////////////////////////////////
    //
    //                        XOR-BASED MULTI-PORTED RAM
    //
    // For reference, see Laforest et al.'s "Composing Multi-Ported Memories on
    // FPGAs", DOI: http://dx.doi.org/10.1145/2629629, or following summary:
    // https://tomverbeure.github.io/2019/08/03/Multiport-Memories.html
    //
    // Following table shows the read address assignment for each RAM block,
    // with ARx corresponding to the address requested by read port x (RPx) and
    // AWy is the address specified by write port y (WPy).  The table also
    // features internal read ports (IPz) for loopback data required during
    // writes (each write port must read from all other columns to compose the
    // actual XORed write data).
    //
    //  n = PORTS_RD (number of read ports)
    //  m = PORTS_WR (number of write ports)
    //
    //              |      n read ports       | m-1 internal read ports |
    //
    //                RP0   RP1         RPn-1   IP0   IP1         IPm-2
    // -----        +-----+-----+     +-------+-----+-----+     +-------+
    //          WP0 | AR0 | AR1 | ... | ARn-1 | AW1 | AW2 | ... | AWm-1 |
    //              +-----+-----+     +-------+-----+-----+     +-------+
    //   m      WP1 | AR0 | AR1 | ... | ARn-1 | AW0 | AW2 | ... | AWm-1 |
    // write        +-----+-----+     +-------+-----+-----+     +-------+
    // ports          ...   ...          ...    ...   ...          ...
    //              +-----+-----+     +-------+-----+-----+     +-------+
    //          WPm | AR0 | AR1 | ... | ARn-1 | AW0 | AW1 | ... | AWm-2 |
    // -----        +-----+-----+     +-------+-----+-----+     +-------+
    //
    // There is one row for each write port. The read ports have an individual
    // column each, which is used to read data from every row.  Note that the
    // first n columns are for the n read ports, followed by m-1 columns for
    // the m write ports (one column less than write ports) which a write port
    // requires to read back data from all other rows.  We save one internal
    // read port by removing the redundant diagonal where WPy == IPy.
    //

    localparam int unsigned PORTS_RD_TOTAL = PORTS_RD + PORTS_WR - 1;

    // read address assignment
    logic [4+$clog2(VREG_W/PORT_W):0] rd_addr[PORTS_RD_TOTAL][PORTS_WR];
    always_comb begin
        for (int i = 0; i < PORTS_RD; i++) begin
            for (int j = 0; j < PORTS_WR; j++) begin
                rd_addr[i][j] = rd_addr_i[i];
            end
        end
        for (int i = 0; i < PORTS_WR - 1; i++) begin
            for (int j = 0; j < PORTS_WR; j++) begin
                rd_addr[PORTS_RD + i][j] = (i < j) ? wr_addr_i[i] : wr_addr_i[i+1];
            end
        end
    end

    // RAM instantiation
    logic [PORT_W-1:0] rd_data[PORTS_RD_TOTAL][PORTS_WR];
    generate
        for (genvar gw = 0; gw < PORTS_WR; gw++) begin

            // compose write data
            logic [PORT_W-1:0] wr_data;
            always_comb begin
                wr_data = wr_data_i[gw];
                for (int i = 0; i < PORTS_WR - 1; i++) begin
                    if (i < gw) begin
                        wr_data = wr_data ^ rd_data[PORTS_RD+gw-1][i  ];
                    end else begin
                        wr_data = wr_data ^ rd_data[PORTS_RD+gw  ][i+1];
                    end
                end
            end

            case (RAM_TYPE)

                vproc_pkg::RAM_GENERIC: begin
                    for (genvar gr = 0; gr < PORTS_RD_TOTAL; gr++) begin
                        logic [VREG_W-1:0] ram[32];
                        always_ff @(posedge clk_i) begin
                            for (int i = 0; i < PORT_W / 8; i++) begin
                                if (wr_we_i[gw] & wr_be_i[gw][i]) begin
                                    ram[wr_addr_i[gw]][i*8 +: 8] <= wr_data[i*8 +: 8];
                                end
                            end
                        end
                        assign rd_data[gr][gw] = ram[rd_addr[gr][gw]];
                    end
                end

                vproc_pkg::RAM_XLNX_RAM32M: begin
                    // use Xilinx's 2-bit wide by 32-deep RAM32M primitive with
                    // one write port and three independent read ports
                    for (genvar gr = 0; gr < (PORTS_RD_TOTAL + 2) / 3; gr++) begin
                        for (genvar gm = 0; gm < PORT_W / 2; gm++) begin
                            logic [4+$clog2(VREG_W/PORT_W):0] rd_addr_0, rd_addr_1, rd_addr_2;
                            logic [                      1:0] rd_data_0, rd_data_1, rd_data_2;
                            RAM32M xlnx_ram32m_inst (
                                .DOA    ( rd_data_0                       ),
                                .DOB    ( rd_data_1                       ),
                                .DOC    ( rd_data_2                       ),
                                .DOD    (                                 ),
                                .ADDRA  ( rd_addr_0                       ),
                                .ADDRB  ( rd_addr_1                       ),
                                .ADDRC  ( rd_addr_2                       ),
                                .ADDRD  ( wr_addr_i[gw]                   ),
                                .DIA    ( wr_data[2*gm +: 2]              ),
                                .DIB    ( wr_data[2*gm +: 2]              ),
                                .DIC    ( wr_data[2*gm +: 2]              ),
                                .DID    ( wr_data[2*gm +: 2]              ),
                                .WCLK   ( clk_i                           ),
                                .WE     ( wr_we_i[gw] & wr_be_i[gw][gm/4] )
                            );
                            assign rd_addr_0                    = rd_addr[gr*3][gw];
                            assign rd_data[gr*3][gw][2*gm +: 2] = rd_data_0;
                            if (gr*3+1 < PORTS_RD_TOTAL) begin
                                assign rd_addr_1                      = rd_addr[gr*3+1][gw];
                                assign rd_data[gr*3+1][gw][2*gm +: 2] = rd_data_1;
                            end else begin
                                assign rd_addr_1                      = '0;
                            end
                            if (gr*3+2 < PORTS_RD_TOTAL) begin
                                assign rd_addr_2                      = rd_addr[gr*3+2][gw];
                                assign rd_data[gr*3+2][gw][2*gm +: 2] = rd_data_2;
                            end else begin
                                assign rd_addr_2                      = '0;
                            end
                        end
                    end
                end

                default: ;

            endcase
        end
    endgenerate

    // compose read data
    always_comb begin
        for (int i = 0; i < PORTS_RD; i++) begin
            rd_data_o[i] = rd_data[i][0];
            for (int j = 1; j < PORTS_WR; j++) begin
                rd_data_o[i] = rd_data_o[i] ^ rd_data[i][j];
            end
        end
    end

endmodule
