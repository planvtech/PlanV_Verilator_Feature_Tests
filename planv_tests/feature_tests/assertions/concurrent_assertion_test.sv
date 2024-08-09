module concurrent_assertion_test;
    bit clk;
    bit [3:0] counter;

    always #5 clk = ~clk;

    initial begin
        clk = 0;
        counter = 0;
        repeat(10) @(posedge clk) counter++;
        $finish;
    end

    // Concurrent assertion: Verify that the counter increments with each clock cycle
    property p1;
        @(posedge clk) disable iff (counter == 0) counter == $past(counter) + 1;
    endproperty

    assert property (p1) else $fatal("Test failed: counter did not increment correctly");
endmodule
