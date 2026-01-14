// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: conditional coverage collection

`include "test_utils.svh"

module t_cov_iff_basic;
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

        // NOTE: covergroup.print() is not defined in IEEE 1800 standard
        `DBG(("Coverage collected: %0.2f%%", $get_coverage()))
        `TEST_PASS  // End marker
    end
endmodule
