// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: basic functional coverage collection

`include "test_utils.svh"

module t_cov_coverpoint_basic;
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

        // NOTE: covergroup.print() is not defined in IEEE 1800 standard
        `DBG(("Coverage collected: %0.2f%%", $get_coverage()))
        `TEST_PASS  // End marker
    end
endmodule
