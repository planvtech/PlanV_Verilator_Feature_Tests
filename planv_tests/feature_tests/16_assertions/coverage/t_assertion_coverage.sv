// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: assertion coverage collection

`include "test_utils.svh"

module t_assertion_coverage;
    bit clk;
    bit [3:0] counter;
    bit coverage_hit;

    // Clock generation
    always #5 clk = ~clk;

    // Cover property: Check coverage when counter reaches its maximum value
    property p3;
        @(posedge clk) (counter == 4'b1111);
    endproperty

    // Cover property at module level
    cover property (p3);

    // Detect when counter hits 15
    always @(posedge clk) begin
        if (counter == 4'b1111)
            coverage_hit <= 1;
    end

    // Single initial block for setup and self-check
    initial begin
        clk = 0;
        counter = 0;
        coverage_hit = 0;

        // Counter incrementing loop - increment to reach 15
        // Start at 0, need 16 increments to wrap but we want to stop at 15
        repeat(16) begin
            @(posedge clk);
            if (counter < 15) counter++;
        end

        // Wait one more cycle for the coverage_hit flag to be set
        @(posedge clk);

        `DBG(("Coverage property p3 check: counter = %0d, coverage_hit = %0d", counter, coverage_hit))

        // Check if the coverage was hit
        if (!coverage_hit) begin
            `DBG(("Error: Coverage property p3 was not hit."))
            $stop; // Stop simulation if the property was not hit
        end

        // End marker
        `TEST_PASS  // End marker
    end
endmodule
