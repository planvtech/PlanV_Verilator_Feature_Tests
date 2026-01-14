// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints with constraint_mode() disabled

`include "test_utils.svh"

class inner;
    rand int val;
    function new();
        val = 0;
    endfunction
endclass

class Foo;
   rand inner in;
   rand int x;
   function new();
         in = new();
        x = 2;
   endfunction
endclass

class Cls;
   rand Foo foo;
   rand int y;

   constraint c_1 {
      foo.x < y;
      foo.x > foo.in.val;
      y < 5;
      foo.in.val > 0;
   }

   function new();
       foo = new();
       y = 0;
   endfunction
endclass

module t_global_inline_disabled;

   Cls obj;
   int res;

   initial begin
      obj = new();
      res = obj.randomize();
      `DBG(("Randomization result: %0d, foo.x: %0d, y: %0d, foo.in.val: %0d", res, obj.foo.x, obj.y, obj.foo.in.val))
      `TEST_PASS
   end
endmodule
