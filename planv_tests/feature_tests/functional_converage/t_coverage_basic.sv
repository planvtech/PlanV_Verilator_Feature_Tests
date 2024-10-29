// DESCRIPTION: PlanV Verilator Basic Coverage Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

module t_coverage_basic;
    bit [7:0] value;

    // Coverage group to capture all values of `value`
    covergroup value_coverage;
        cp_value: coverpoint value;
    endgroup

    value_coverage vcg = new();

    initial begin
        // Iterate through all possible values of 8-bit `value`
        for (int i = 0; i < 256; i++) begin
            value = i;
            vcg.sample();  // Sample the coverage point
        end

        // Print the coverage report
        vcg.print();  
        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
