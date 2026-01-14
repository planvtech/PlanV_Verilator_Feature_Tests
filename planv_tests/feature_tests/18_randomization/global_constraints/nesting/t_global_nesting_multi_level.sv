// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints with multi-level class nesting

`include "test_utils.svh"

class Sub_sub;
    rand bit [3:0] val;
    constraint c { val == 3; }
    function new();
        val = 0; // Initialize to 0
    endfunction
endclass

class Sub;
    rand Sub_sub inner;
    rand bit [3:0] val;
    constraint c { val == 4; }
    function new();
        inner = new();
        val = 0;
    endfunction
endclass

class Top;
    rand Sub obj;
    rand bit [3:0] val;
    constraint c { val == 5; }
    function new();
        obj = new();
        val = 0; // Initialize to 0
    endfunction
endclass

module t_global_nesting_multi_level;
    Top t = new();
    initial begin
        if (!t.randomize()) $stop;
        `DBG(("T1: val = %0d, obj.val = %0d, obj.inner.val = %0d", t.val, t.obj.val, t.obj.inner.val))
        if (t.val !== 5) $stop;
        if (t.obj.val !== 4) $stop;
        if (t.obj.inner.val !== 3) $stop;
        `TEST_PASS
    end
endmodule