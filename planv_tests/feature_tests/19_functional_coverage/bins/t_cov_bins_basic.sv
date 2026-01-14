// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: coverage bin definition and sampling

`include "test_utils.svh"

module t_cov_bins_basic;
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
        // Iterate through all possible values of 8-bit `value`
        for (int i = 0; i < 256; i++) begin
            value = i;
            vbc.sample();  // Sample the coverage point
        end

        // NOTE: covergroup.print() is not defined in IEEE 1800 standard
        `DBG(("Coverage collected: %0.2f%%", $get_coverage()))
        `TEST_PASS  // End marker
    end
endmodule
