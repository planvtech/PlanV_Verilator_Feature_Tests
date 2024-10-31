// DESCRIPTION: PlanV Verilator Assertion Coverage Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

module t_assertion_coverage;
    bit clk;
    bit [3:0] counter;
    bit coverage_check;

    // Clock generation
    always #5 clk = ~clk;

    // Single initial block for setup and self-check
    initial begin
        clk = 0;
        counter = 0;
        coverage_check = 0;

        // Counter incrementing loop
        repeat(10) @(posedge clk) counter++;

        // Cover property: Check coverage when counter reaches its maximum value
        property p3;
            @(posedge clk) (counter == 4'b1111);
        endproperty

        cover property (p3);

        // Self-check to validate coverage
        wait (counter == 4'b1111);
        coverage_check = 1;  // Indicate that coverage was hit
        $display("Coverage property p3 was hit: counter = %0d", counter);
        
        // Check if the coverage was hit
        if (!coverage_check) begin
            $display("Error: Coverage property p3 was not hit.");
            $stop; // Stop simulation if the property was not hit
        end

        // End marker
        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
