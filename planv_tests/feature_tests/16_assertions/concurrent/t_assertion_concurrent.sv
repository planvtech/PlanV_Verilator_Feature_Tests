// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: concurrent assertion evaluation

`include "test_utils.svh"

module t_assertion_concurrent;
    bit clk;
    bit [3:0] counter;
    bit started;

    // Clock generation
    always #5 clk = ~clk;

    // Property: Verify that the counter increments with each clock cycle
    // Only check after counter has started incrementing (counter > 0)
    property p1;
        @(posedge clk) (started && counter > 0) |-> (counter == $past(counter) + 1);
    endproperty

    // Assert property at module level
    assert property (p1) else $fatal(1, "Test failed: counter did not increment correctly");

    // Combined initial block for setup and end marker
    initial begin
        clk = 0;
        counter = 0;
        started = 0;

        @(posedge clk);
        started = 1;
        repeat(10) @(posedge clk) counter++;

        `TEST_PASS  // End marker
    end
endmodule
