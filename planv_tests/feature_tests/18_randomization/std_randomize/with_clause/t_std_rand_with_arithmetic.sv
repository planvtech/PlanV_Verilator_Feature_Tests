// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: std::randomize() with multiple variables

`include "test_utils.svh"

class Packet;
   rand int a;
   rand int b;

   function new();
      a = 0;
      b = 0;
   endfunction
endclass

module t_std_rand_with_arithmetic;
   initial begin
      Packet p;
      p = new;

      // Test 1: Multiplication in with clause
      if (p.randomize() with { a > 0; a < 5; b == a * 2; } != 1) $stop;
      if (!(p.a > 0 && p.a < 5 && p.b == p.a * 2)) $stop;
      `DBG(("Test 1 passed: a=%0d, b=%0d (b == a*2)", p.a, p.b))

      // Test 2: Division in with clause
      if (p.randomize() with { a > 10; a < 20; a % 2 == 0; b == a / 2; } != 1) $stop;
      if (!(p.a > 10 && p.a < 20 && p.a % 2 == 0 && p.b == p.a / 2)) $stop;
      `DBG(("Test 2 passed: a=%0d, b=%0d (b == a/2)", p.a, p.b))

      // Test 3: Addition and multiplication
      if (p.randomize() with { a > 5; a < 10; b == a * 3 + 1; } != 1) $stop;
      if (!(p.a > 5 && p.a < 10 && p.b == p.a * 3 + 1)) $stop;
      `DBG(("Test 3 passed: a=%0d, b=%0d (b == a*3+1)", p.a, p.b))

      `TEST_PASS
   end
endmodule
