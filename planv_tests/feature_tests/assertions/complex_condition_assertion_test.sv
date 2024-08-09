module complex_condition_assertion_test;
    bit clk;
    bit [3:0] counter;
    bit [3:0] threshold = 4'd8;

    always #5 clk = ~clk;

    initial begin
        clk = 0;
        counter = 0;
        repeat(10) @(posedge clk) counter++;
        $finish;
    end

    // Concurrent assertion: Verify that when the counter exceeds the threshold, it must reset to 0 within two clock cycles
    property p4;
        @(posedge clk) disable iff (counter == 0) (counter > threshold) |-> ##2 (counter == 0);
    endproperty

    assert property (p4) else $fatal("Test failed: counter did not reset as expected");
endmodule
