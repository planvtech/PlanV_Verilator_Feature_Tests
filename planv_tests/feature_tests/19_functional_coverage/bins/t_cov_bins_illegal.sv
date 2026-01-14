// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: illegal bins in coverage definitions

`include "test_utils.svh"

module t_cov_bins_illegal;
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
        // NOTE: covergroup.print() is not defined in IEEE 1800 standard
        `DBG(("Coverage collected: %0.2f%%", $get_coverage()))
        `TEST_PASS  // End marker
    end
endmodule
