// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints in class inheritance

`include "test_utils.svh"

class Base;
    rand bit [3:0] val1;
endclass

class Derived extends Base;
    rand bit [3:0] val2;

    constraint c_Derived {
        val2 > val1;
        val1 inside {[2:4]};
        val2 <= 5;
    }

    function new();
        super.new();
        val1 = 1;
        val2 = 1;
    endfunction

    function void display();
        `DBG(("Derived: val1 = %0d, val2 = %0d", val1, val2))
    endfunction

endclass

module t_global_inherit_basic;
    bit success, valid;
    Derived obj;

    initial begin
        obj = new();
        success = obj.randomize();
        valid = success && (obj.val1 < obj.val2) && (obj.val1 inside {[2:4]});
        if (!valid) $stop;
        obj.display();
        `TEST_PASS
    end
endmodule
