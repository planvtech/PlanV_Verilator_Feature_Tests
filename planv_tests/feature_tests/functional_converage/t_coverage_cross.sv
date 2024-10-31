// DESCRIPTION: PlanV Verilator Cross Coverage Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

module t_coverage_cross;
    bit [3:0] a, b;

    // Coverage group to capture cross coverage of `a` and `b`
    covergroup ab_coverage;
        cp_a: coverpoint a;
        cp_b: coverpoint b;
        cross_ab: cross cp_a, cp_b;  // Cross coverage of `a` and `b`
    endgroup

    ab_coverage ab_cg = new();

    initial begin
        for (int i = 0; i < 16; i++) begin
            for (int j = 0; j < 16; j++) begin
                a = i;
                b = j;
                ab_cg.sample();  // Sample the coverage points and cross
            end
        end
        ab_cg.print();  // Print the coverage report
        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
