// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints with rand_mode() control

`include "test_utils.svh"

class RandomValue;
  rand int value;
  constraint small_int_c {
    value < 10;
  }
  task disable_val();
    value.rand_mode(0);
  endtask
endclass

class Base;
  rand RandomValue v = new;
endclass

class Foo extends Base;
endclass

module t_global_inline_rand_mode;
  initial begin
    Foo d = new;
    Base b = d;
    b.v.disable_val();
    b.v.value = 11;
    if (bit'(b.randomize())) $stop;
    if (b.v.value != 11) $stop;
    `TEST_PASS
  end
endmodule
