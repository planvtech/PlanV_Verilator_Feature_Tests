// DESCRIPTION: PlanV Verilator Complex Condition Assertion Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

module t_assertion_condition;
    bit clk;
    bit [3:0] counter;
    bit [3:0] threshold = 4'd8;

    // Clock generation
    always #5 clk = ~clk;

    // Single initial block for setup and self-check
    initial begin
        clk = 0;
        counter = 0;
        // Counter incrementing loop
        repeat(10) @(posedge clk) counter++;

        // Concurrent assertion: Verify that when the counter exceeds the threshold, it must reset to 0 within two clock cycles
        property p4;
            @(posedge clk) disable iff (counter == 0) (counter > threshold) |-> ##2 (counter == 0);
        endproperty

        // Assert the property with self-checking
        assert property (p4) else begin
            $fatal("Test failed: counter did not reset as expected");
        end

        // End marker
        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
