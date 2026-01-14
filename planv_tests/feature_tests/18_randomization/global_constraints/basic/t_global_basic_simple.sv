// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: basic global constraint syntax

`include "test_utils.svh"

class A;
    rand bit [7:0] v;

    function new();
    endfunction
endclass

class B extends A;
    rand A left;
    rand A right;

    constraint heapcond {
        left.v <= v;
        right.v > v;
    }

    function new();
        left = new();
        right = new();
    endfunction
endclass

module t_global_basic_simple;
    B obj = new();

    initial begin
        if (!obj.randomize()) $fatal("Randomization failed.");

        // Display the values of the heap node and its children
        `DBG(("Heap node value: %0d", obj.v))
        `DBG(("Left child value: %0d", obj.left.v))
        `DBG(("Right child value: %0d", obj.right.v))

        // Validate constraints
        if (!(obj.left.v <= obj.v)) begin
            `DBG(("Constraint violated: left.v = %0d, v = %0d", obj.left.v, obj.v))
            $stop;
        end
        if (!(obj.right.v > obj.v)) begin 
            `DBG(("Constraint violated: right.v = %0d, v = %0d", obj.right.v, obj.v))
            $stop;
        end

        `DBG(("Global constraints test passed."))
        `TEST_PASS
    end
endmodule
