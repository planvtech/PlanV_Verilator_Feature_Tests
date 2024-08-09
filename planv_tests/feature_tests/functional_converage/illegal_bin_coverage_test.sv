module illegal_bin_coverage_test;
    bit [3:0] value;

    // Coverage group to capture legal and illegal values
    covergroup value_illegal_coverage;
        cp_value: coverpoint value {
            bins legal = {[0:14]};         // Legal values
            illegal_bins illegal = {15};   // Illegal value
        }
    endgroup

    value_illegal_coverage vicg = new();

    initial begin
        for (int i = 0; i < 16; i++) begin
            value = i;
            vicg.sample();  // Sample the coverage point
        end
        vicg.print();  // Print the coverage report
        $finish;
    end
endmodule
