// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: simple global constraints on nested members

`include "test_utils.svh"

module t_global_basic_nested_simple;

    // Simple inner class
    class DataClass;
        rand int value;
        constraint basic { value inside {[1:50]}; }
    endclass

    // Container class
    class Container;
        rand DataClass data;
        function new(); data = new(); endfunction
    endclass

    // Test class with global constraints
    class SimpleTest;
        rand Container obj1;
        rand Container obj2;

        function new();
            obj1 = new();
            obj2 = new();
        endfunction

        // This is the KEY constraint that tests the nested MemberSel fix
        constraint global_nested {
            // Two-level nesting: obj1.data.value
            // This should FAIL on old version, WORK on new version
            obj1.data.value + obj2.data.value < 80;
            obj1.data.value != obj2.data.value;
        }

        function void display();
            `DBG(("obj1.data.value = %0d", obj1.data.value))
            `DBG(("obj2.data.value = %0d", obj2.data.value))
            `DBG(("Sum = %0d (should be < 80)", obj1.data.value + obj2.data.value))
        endfunction
    endclass

    initial begin
        SimpleTest test;
        `DBG(("=== Simple Nested Constraint Test ==="))
        `DBG(("Testing: obj1.data.value + obj2.data.value < 80"))

        test = new();
        if (test.randomize()) begin
            `DBG(("SUCCESS: Randomization worked!"))
            test.display();
        end else begin
            `DBG(("FAILED: Randomization failed (likely old version issue)"))
        end
        `TEST_PASS
    end

endmodule