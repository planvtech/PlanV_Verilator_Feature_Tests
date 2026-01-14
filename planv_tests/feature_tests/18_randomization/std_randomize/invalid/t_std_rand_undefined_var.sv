// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: std::randomize() with undefined variables (error case)
//
// TEST_NEGATIVE: Expected compilation failure
// EXPECTED_ERROR: (vlog-2730) Undefined variable: 'b'
// VERIFIED: 2026-01-13 - QuestaSim correctly rejects undefined variable in std::randomize()

`include "test_utils.svh"

module t_std_rand_undefined_var;
    bit [3:0] a;

    function void define();
        bit b;
    endfunction

    function bit run();
        bit success;
        success = std::randomize(a, b); // ❌ ERROR: addr is not declared in current scope
        return success;
    endfunction

    initial begin
        bit ok;
        ok = run();
        `DBG(("ok=%0d", ok))
        if (!ok) $stop;
    end
endmodule
