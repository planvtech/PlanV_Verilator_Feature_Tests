// DESCRIPTION: PlanV Verilator Illegal Bin Coverage Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

module t_coverage_illegalBin;
    bit [3:0] value;

    // Coverage group to capture legal and illegal values
    covergroup value_illegal_coverage;
        cp_value: coverpoint value {
            bins legal = {[0:14]};         // Legal values
            illegal_bins illegal = {15};    // Illegal value
        }
    endgroup

    value_illegal_coverage vicg = new();

    initial begin
        for (int i = 0; i < 16; i++) begin
            value = i;
            vicg.sample();  // Sample the coverage point
        end
        vicg.print();  // Print the coverage report
        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
