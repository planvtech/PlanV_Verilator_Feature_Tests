// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: std::randomize() with local variables in class method (scope error)

`include "test_utils.svh"

class Cls;
  function int do_randomize();
    int x;  // Local variable
    int success;
    success = std::randomize(x);  // ❌ ERROR: x is local to function, not accessible to std::randomize
    return success;
  endfunction
endclass

module t_std_rand_invalid_scope;
  initial begin
    automatic Cls c = new;
    automatic int result;
    result = c.do_randomize();
    `DBG(("Result: %0d", result))
    `TEST_PASS
  end
endmodule
