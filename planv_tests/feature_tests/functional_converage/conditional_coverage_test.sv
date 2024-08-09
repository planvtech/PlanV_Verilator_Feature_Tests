module conditional_coverage_test;
    bit [3:0] value;
    bit enable;

    // Coverage group to capture value only when enable is set
    covergroup conditional_coverage;
        cp_value: coverpoint value {
            bins enabled = {0, 1, 2, 3} iff (enable == 1'b1);
        }
    endgroup

    conditional_coverage ccg = new();

    initial begin
        enable = 1'b0;
        for (int i = 0; i < 16; i++) begin
            value = i;
            ccg.sample();  // Sample coverage point only when condition is met
        end

        enable = 1'b1;
        for (int i = 0; i < 16; i++) begin
            value = i;
            ccg.sample();  // Sample coverage point only when condition is met
        end

        ccg.print();  // Print the coverage report
        $finish;
    end
endmodule
