// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: std::randomize() with invalid arguments
//
// TEST_NEGATIVE: Expected compilation failure
// EXPECTED_ERROR: (vlog-2931) Invalid argument #1 for randomize() function
// VERIFIED: 2026-01-13 - QuestaSim correctly rejects expression argument to std::randomize()

`include "test_utils.svh"

module t_std_rand_invalid_expr;
    bit [3:0] a;

    function bit run();
        bit success;
        success = std::randomize(a + 1); // ❌ ERROR: argument is not a variable
        `DBG(("a=%0h", a))
        return success;
    endfunction

    initial begin
        bit ok;
        ok = run();
        `DBG(("ok=%0d", ok))
        if (!ok) $stop;
    end
endmodule
