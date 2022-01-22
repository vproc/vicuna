// Copyright TU Wien
// Licensed under the ISC license, see LICENSE.txt for details
// SPDX-License-Identifier: ISC

    // Assert that the vreg read address corresponds to the register being fetched
    assert property (
        @(posedge clk_i)
        (state_init_valid & state_init.vs1_fetch) |-> (vreg_rd_addr_o == state_init.rs1.r.vaddr)
    ) else begin
        $error("vreg_rd_addr_o incorrect while fetching vs1");
    end
    assert property (
        @(posedge clk_i)
        (BUF_VREG ? (state_vreg_valid_q & state_vreg_q.vs2_fetch) : (state_vs1_valid_q & state_vs1_q.vs2_fetch)) |->
        (vreg_rd_addr_o == (BUF_VREG ? state_vreg_q.rs2.r.vaddr : state_vs1_q.rs2.r.vaddr))
    ) else begin
        $error("vreg_rd_addr_o incorrect while fetching vs2");
    end

    // Assert that a vreg is still in the pending reads while being fetched
    assert property (
        @(posedge clk_i)
        (state_init_valid & ~state_init_stall & state_init.vs1_fetch) |-> vreg_pend_rd_o[state_init.rs1.r.vaddr]
    ) else begin
        $error("vs1 not in vreg_pend_rd_o while fetching");
    end
    assert property (
        @(posedge clk_i)
        (BUF_VREG ? (state_vreg_valid_q & state_vreg_q.vs2_fetch) : (state_vs1_valid_q & state_vs1_q.vs2_fetch)) |->
        vreg_pend_rd_o[BUF_VREG ? state_vreg_q.rs2.r.vaddr : state_vs1_q.rs2.r.vaddr]
    ) else begin
        $error("vs2 not in vreg_pend_rd_o while fetching");
    end
    assert property (
        @(posedge clk_i)
        (state_vs1_valid_q & state_vs1_masked & state_vs1_q.first_cycle) |-> vreg_pend_rd_o[0]
    ) else begin
        $error("v0 (mask) not in vreg_pend_rd_o while fetching");
    end

    // Assert that local pending writes are only added in the first cycle of an instruction
    // Assert that new vregs are added to the pending reads only in the first cycle of an instruction or when local pending writes are cleared
    generate
        for (genvar g = 0; g < 32; g++) begin
            assert property (
                @(posedge clk_i)
                $rose(vreg_pend_wr_q[g]) |-> state_init.first_cycle
            ) else begin
                $error("local pending write for vreg %d added midway", g);
            end
            assert property (
                @(posedge clk_i)
                $rose(vreg_pend_rd_o[g]) |-> (state_init.first_cycle | $fell(vreg_pend_wr_q[g]))
            ) else begin
                $error("pending read for vreg %d added midway", g);
            end
        end
    endgenerate

    // Assert that a vreg is still in the pending writes while being written
    assert property (
        @(posedge clk_i)
        vreg_wr_en_o |-> vreg_pend_wr_i[vreg_wr_addr_o]
    ) else begin
        $error("writing to a vreg which is not in the global pending writes");
    end
    assert property (
        @(posedge clk_i)
        vreg_wr_en_o |-> (~vreg_pend_rd_i[vreg_wr_addr_o])
    ) else begin
        $error("writing to a vreg for which there are pending reads");
    end
