// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints with polymorphic class members

`include "test_utils.svh"

class A;
  rand int x;
endclass

class B extends A;
  constraint c {x == 1;};
endclass

class C;
  rand A a;
  constraint c {a.x < 100;};
endclass

module t_global_inherit_polymorphism;
  initial begin
    C c = new;
    B b = new;
    c.a = b;  // Assign B instance to polymorphic A handle
    void'(c.randomize());
    `DBG(("Randomized value: c.a.x = %0d", c.a.x))
    // c.a is type B, so constraint B::c applies (x == 1)
    // Also C::c applies (a.x < 100)
    // Both are satisfied when x == 1
    if (c.a.x != 1) $stop;
    `TEST_PASS
  end
endmodule
