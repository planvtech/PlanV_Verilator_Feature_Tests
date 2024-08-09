module basic_coverage_test;
    bit [7:0] value;

    // Coverage group to capture all values of `value`
    covergroup value_coverage;
        cp_value: coverpoint value;
    endgroup

    value_coverage vcg = new();

    initial begin
        for (int i = 0; i < 256; i++) begin
            value = i;
            vcg.sample();  // Sample the coverage point
        end
        vcg.print();  // Print the coverage report
        $finish;
    end
endmodule
