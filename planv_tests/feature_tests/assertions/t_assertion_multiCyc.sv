// DESCRIPTION: PlanV Verilator Multi-Cycle Assertion Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

module t_assertion_multiCyc;
    bit clk;
    bit rst_n;
    bit [3:0] counter;

    // Clock generation
    always #5 clk = ~clk;

    initial begin
        clk = 0;
        rst_n = 1;
        counter = 0;

        // Reset logic
        repeat(2) @(posedge clk);
        rst_n = 0;  // Active low reset
        repeat(1) @(posedge clk);
        rst_n = 1;  // Release reset

        // Counter increment
        repeat(10) @(posedge clk) counter++;

        // End simulation
        $finish;
    end

    // Concurrent assertion: After reset, counter should be 0 within two clock cycles
    property p2;
        @(posedge clk) disable iff (!rst_n) (rst_n && counter == 0) |-> ##2 (counter == 0);
    endproperty

    // Assert the property with self-checking
    assert property (p2) else $fatal("Test failed: counter did not reset correctly");

    // End marker
    initial begin
        @(posedge clk);
        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
