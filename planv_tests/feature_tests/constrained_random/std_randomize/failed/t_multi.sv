// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int a;
   rand int b;

   function new();
      a = 0;
      b = 0;
   endfunction
endclass

module t_multi;
   initial begin
      Packet p;
      p = new;

      // Test 1: Multiplication in with clause
      if (p.randomize() with { a > 0; a < 5; b == a * 2; } != 1) $stop;
      if (!(p.a > 0 && p.a < 5 && p.b == p.a * 2)) $stop;
      $display("Test 1 passed: a=%0d, b=%0d (b == a*2)", p.a, p.b);

      // Test 2: Division in with clause
      if (p.randomize() with { a > 10; a < 20; a % 2 == 0; b == a / 2; } != 1) $stop;
      if (!(p.a > 10 && p.a < 20 && p.a % 2 == 0 && p.b == p.a / 2)) $stop;
      $display("Test 2 passed: a=%0d, b=%0d (b == a/2)", p.a, p.b);

      // Test 3: Addition and multiplication
      if (p.randomize() with { a > 5; a < 10; b == a * 3 + 1; } != 1) $stop;
      if (!(p.a > 5 && p.a < 10 && p.b == p.a * 3 + 1)) $stop;
      $display("Test 3 passed: a=%0d, b=%0d (b == a*3+1)", p.a, p.b);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
