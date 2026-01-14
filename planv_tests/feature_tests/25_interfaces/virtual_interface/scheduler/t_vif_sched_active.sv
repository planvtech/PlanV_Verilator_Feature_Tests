// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: scheduler active region with virtual interfaces

`include "test_utils.svh"

interface Bus;
    logic [15:0] data;
endinterface

module t_vif_sched_active;
    logic clk = 0;
    integer cyc = 0;
    Bus intf();
    virtual Bus vif = intf;
    logic [15:0] data;

    always @(posedge clk) begin
        cyc <= cyc + 1;
    end

    // Finish on negedge so that $finish is last
    always @(negedge clk) begin
        if (cyc >= 6) begin
            `TEST_PASS
        end
    end

    always @(posedge clk) begin
        if (cyc == 1) intf.data <= 'hdead;
        else if (cyc == 2) intf.data <= 'hbeef;
        else if (cyc == 3) intf.data <= 'hface;
        else if (cyc == 4) intf.data <= 'hcafe;
    end

    always @(negedge clk) begin
        data <= vif.data;
    end
    /*
    always @(intf.data) begin
        $write("[%0t] intf.data==%h\n", $time, intf.data);
    end
    always @(vif.data) begin
        $write("[%0t] vif.data==%h\n", $time, vif.data);
    end
    */
    always @(data) begin
        `DBG(("[%0t] data==%h", $time, data))
    end

    initial begin
        repeat (20) #5ns clk = ~clk;
    end

endmodule
