// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints referencing nested non-rand config members

`include "test_utils.svh"

class Cfg;
  bit [7:0] limit = 120;  // non-rand member
endclass

class Payload;
  rand bit [7:0] data;
  Cfg cfg = new();  // non-rand object

  function bit run();
    return randomize() with { data <= cfg.limit; data > 119; };  // reference nested non-rand
  endfunction
endclass

module t_global_member_sel_nested_cfg;
  Payload p = new();
  bit success;

  initial begin
    success = p.run();
    if (!success) $stop;
    `DBG(("data = %0d, limit = %0d", p.data, p.cfg.limit))
    if (p.data > p.cfg.limit) $stop;

    // Successful execution marker
    `TEST_PASS
  end
endmodule
