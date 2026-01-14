// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints across class member boundaries

`include "test_utils.svh"

class Sub;
    rand bit [3:0] arr[2];
    constraint c { arr[0] == 5; }
endclass

class Top;
    rand Sub obj;
    function new();
        obj = new();
        obj.arr[0] = 10; // Initialize the first element to 10
    endfunction
endclass

module t_global_basic_cross_member;
    Top t = new();
    initial begin
        if (!t.randomize()) $stop;
        `DBG(("T6: obj.arr[0] = %0d", t.obj.arr[0]))
        if (t.obj.arr[0] !== 5) $stop;
        `TEST_PASS
    end
endmodule