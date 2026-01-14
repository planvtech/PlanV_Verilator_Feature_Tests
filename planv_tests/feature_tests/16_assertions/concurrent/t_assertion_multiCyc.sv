// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: multi-cycle assertion behavior

`include "test_utils.svh"

module t_assertion_multiCyc;
    bit clk;
    bit rst_n;
    bit [3:0] counter;

    // Clock generation
    always #5 clk = ~clk;

    // Property: After reset deasserted, counter should increment
    // Check that counter increments properly when not in reset
    property p2;
        @(posedge clk) disable iff (!rst_n) (counter > 0) |-> (counter == $past(counter) + 1);
    endproperty

    // Assert property at module level
    assert property (p2) else $fatal(1, "Test failed: counter did not increment correctly");

    initial begin
        clk = 0;
        rst_n = 0;  // Start in reset
        counter = 0;

        // Release reset after 2 cycles
        repeat(2) @(posedge clk);
        rst_n = 1;  // Release reset

        // Counter increment
        repeat(10) @(posedge clk) counter++;

        `TEST_PASS
    end
endmodule
