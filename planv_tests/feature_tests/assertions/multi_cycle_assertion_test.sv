module multi_cycle_assertion_test;
    bit clk;
    bit rst_n;
    bit [3:0] counter;

    always #5 clk = ~clk;

    initial begin
        clk = 0;
        rst_n = 1;
        counter = 0;
        repeat(2) @(posedge clk);
        rst_n = 0;  // Reset
        repeat(1) @(posedge clk);
        rst_n = 1;
        repeat(10) @(posedge clk) counter++;
        $finish;
    end

    // Concurrent assertion: After reset, counter should be 0 within two clock cycles
    property p2;
        @(posedge clk) disable iff (!rst_n) (rst_n && counter == 0) |-> ##2 (counter == 0);
    endproperty

    assert property (p2) else $fatal("Test failed: counter did not reset correctly");
endmodule
