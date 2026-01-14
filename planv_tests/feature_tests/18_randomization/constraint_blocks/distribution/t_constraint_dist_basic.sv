// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: dist constraint for weighted random distributions

`include "test_utils.svh"

class DistributionConstraintTest;
    rand int value;

    constraint dist_con {
        value dist { [0:9] :/ 25, [10:19] :/ 50, [20:29] :/ 25 };
    }

    function new();
    endfunction
endclass

module t_constraint_dist_basic;
    DistributionConstraintTest dct;

    initial begin
        dct = new();
        repeat(10) begin
            if (!dct.randomize()) $error("Randomization failed");
            `DBG(("value: %0d", dct.value))
        end
        `TEST_PASS
    end
endmodule
