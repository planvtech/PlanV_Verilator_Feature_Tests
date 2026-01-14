// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: this.randomize() resolution in class functions

`include "test_utils.svh"

class Test;
    rand bit enabled;

    constraint cfg_con {
        enabled == 1;
    }

    // This function should randomize with constraints
    function int randomize_test();
        int result;
        result = this.randomize();
        return result;
    endfunction
endclass

module t_randomize_this_in_function;
    initial begin
        Test t = new();
        int result;

        `DBG(("=== Testing this.randomize() in function ==="))

        result = t.randomize_test();

        `DBG(("Randomization returned: %0d", result))
        `DBG(("enabled = %0d (expected: 1)", t.enabled))

        if (result == 1 && t.enabled != 1) begin
            `DBG(("*** BUG: randomize() returned success but constraints not applied! ***"))
            $stop;
        end

        `TEST_PASS
    end
endmodule
