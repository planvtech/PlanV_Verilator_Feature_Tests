// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: complex nesting of global constraints with class members

`include "test_utils.svh"

class Sub;
    int limit; 
    rand bit [3:0] val;
    constraint c1 { val == limit; }

    function new(int x);
        limit = x;
    endfunction
endclass

class Top;
    rand Sub obj1;
    rand Sub obj2;
    rand bit [3:0] val;
    constraint c { val > obj1.val; val < obj2.val; }
    function new();
        obj2 = new(5);
        obj1 = new(3);
    endfunction
endclass

module t_global_nesting_complex;
    Top t = new();
    initial begin
        if (!t.randomize()) $stop;
        `DBG(("T2: obj1.val = %0d, obj2.val = %0d", t.obj1.val, t.obj2.val))
        `DBG(("T2: val = %0d", t.val))
        if (t.val != 4) $stop;
        if (t.obj1.val != 3) $stop;
        if (t.obj2.val != 5) $stop;
        `TEST_PASS
    end
endmodule
