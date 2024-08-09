module assertion_coverage_test;
    bit clk;
    bit [3:0] counter;

    always #5 clk = ~clk;

    initial begin
        clk = 0;
        counter = 0;
        repeat(10) @(posedge clk) counter++;
        $finish;
    end

    // Cover property: Check coverage when counter reaches its maximum value
    property p3;
        @(posedge clk) (counter == 4'b1111);
    endproperty

    cover property (p3);
endmodule
