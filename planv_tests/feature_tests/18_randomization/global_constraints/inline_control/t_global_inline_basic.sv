// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints combined with inline constraints

`include "test_utils.svh"

class Payload;
  rand bit [7:0] data;
endclass

module t_global_inline_basic;
  Payload p = new();
  bit success;
  initial begin
    success = p.randomize() with { data inside {[199:200]}; };
    if (!success) $stop;
    `DBG(("p.data = %0d", p.data))
    if (!(p.data inside {[199:200]})) $stop;

    // Successful execution marker
    `TEST_PASS
  end
endmodule
