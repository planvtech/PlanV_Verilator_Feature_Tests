// DESCRIPTION: PlanV Verilator Concurrent Assertion Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

module t_assertion_concurrent;
    bit clk;
    bit [3:0] counter;

    // Clock generation
    always #5 clk = ~clk;

    // Combined initial block for setup and end marker
    initial begin
        clk = 0;
        counter = 0;
        repeat(10) @(posedge clk) counter++;
        
        // Assert property: Verify that the counter increments with each clock cycle
        property p1;
            @(posedge clk) disable iff (counter == 0) counter == $past(counter) + 1;
        endproperty

        // Check the assertion and handle failure
        assert property (p1) else begin
            $fatal("Test failed: counter did not increment correctly");
        end

        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
