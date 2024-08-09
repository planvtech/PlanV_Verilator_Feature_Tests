module bin_coverage_test;
    bit [7:0] value;

    // Coverage group to capture `value` in specific bins
    covergroup value_bin_coverage;
        cp_value: coverpoint value {
            bins low = {0, 1, 2};          // Bin for values 0, 1, 2
            bins mid = {[3:5]};             // Bin for values 3 to 5
            bins high = {[6:8]};            // Bin for values 6 to 8
            bins overflow = default;        // Catch-all bin for all other values
        }
    endgroup

    value_bin_coverage vbc = new();

    initial begin
        for (int i = 0; i < 256; i++) begin
            value = i;
            vbc.sample();  // Sample the coverage point
        end
        vbc.print();  // Print the coverage report
        $finish;
    end
endmodule
