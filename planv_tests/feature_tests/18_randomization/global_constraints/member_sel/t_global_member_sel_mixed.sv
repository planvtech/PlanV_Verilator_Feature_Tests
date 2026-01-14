// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints referencing non-rand members

`include "test_utils.svh"

class Payload;
  rand bit [7:0] data;
  rand bit [7:0] limit_min;
  bit [7:0] limit_max = 197;  // non-rand member

  function bit run();
    return randomize() with {
      data inside {[190:200]};
      limit_min inside {[180:193]};
      data < limit_max;         // reference non-rand member
      data > limit_min; };
  endfunction
endclass

module t_global_member_sel_mixed;
  Payload p = new();
  bit success, valid;
  initial begin
    success = p.run();
    valid = success && (p.data inside {[190:200]}) && (p.limit_min inside {[180:193]}) && (p.limit_max == 197) && (p.data <= p.limit_max) && (p.data >= p.limit_min);
    
    `DBG(("p.data = %0d, p.limit_min = %0d, p.limit_max = %0d", p.data, p.limit_min, p.limit_max))
    if (!valid) $stop;
    // Successful execution marker
    `TEST_PASS
  end
endmodule

