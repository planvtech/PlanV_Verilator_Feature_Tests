// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints referencing inherited non-rand members

`include "test_utils.svh"

class CfgBase;
  bit [7:0] limit = 50;  // non-rand member in base class
endclass

class Pkg extends CfgBase;
  rand bit [7:0] val;

  function bit test();
    return randomize() with { val <= limit; val > 49; };  // reference inherited non-rand
  endfunction
endclass

module t_global_member_sel_inheritance;
  Pkg p = new();

  initial begin
    if (!p.test()) $stop;
    `DBG(("val = %0d, limit = %0d", p.val, p.limit))
    if (p.val > p.limit) $stop;

    // Successful execution marker
    `TEST_PASS
  end
endmodule
