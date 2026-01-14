// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints with chained member access

`include "test_utils.svh"

class Sub;
    rand bit [3:0] val;
    constraint c { val inside {[1:3]}; }
endclass

class Top;
    rand Sub objs[2];
    function new();
        objs[0] = new();
        objs[1] = new();
    endfunction
endclass

module t_global_array_member_chain;
    Top t = new();
    initial begin
        if (!t.randomize()) $stop;
        foreach (t.objs[i]) begin
            `DBG(("T5: objs[%0d].val = %0d", i, t.objs[i].val))
            if (t.objs[i].val < 1 || t.objs[i].val > 3) $stop;
        end
        `TEST_PASS
    end
endmodule