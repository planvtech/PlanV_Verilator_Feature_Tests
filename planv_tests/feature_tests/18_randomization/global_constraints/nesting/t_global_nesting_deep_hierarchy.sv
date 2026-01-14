// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints in deep class hierarchies

`include "test_utils.svh"

class Inner;
    rand bit [3:0] val;
    constraint c { val == 1; }
endclass

class Mid;
    rand Inner inner;
    rand bit [3:0] val;
    constraint c { val == 2; }
    function new();
        inner = new();
    endfunction
endclass

class Top;
    rand Mid mid;
    function new();
        mid = new();
    endfunction
endclass

module t_global_nesting_deep_hierarchy;
    Top t = new();
    initial begin
        if (!t.randomize()) $stop;
        `DBG(("T4: mid.val = %0d", t.mid.val))
        `DBG(("T4: mid.inner.val = %0d", t.mid.inner.val))
        if (t.mid.val !== 2) $stop;
        if (t.mid.inner.val !== 1) $stop;
        `TEST_PASS
    end
endmodule