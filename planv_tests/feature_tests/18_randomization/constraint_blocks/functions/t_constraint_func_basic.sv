// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: function calls within constraint expressions

`include "test_utils.svh"

class C;
    rand bit [9:0] v;
    rand int length;

    // Function to count the number of ones in a packed array
    function int count_ones(bit [9:0] w);
        for (count_ones = 0; w != 0; w = w >> 1)
            count_ones += w & 1'b1;
    endfunction

    // Constraint using the count_ones function
    constraint count_ones_con {
        length == count_ones(v);
    }

    function new();
    endfunction
endclass

module t_constraint_func_basic;
    C obj = new();
    int i;

    initial begin
        for (i = 0; i < 100; i++) begin
            if (!obj.randomize()) $fatal("Randomization failed.");

            // Display the values
            `DBG(("Randomization %0d:", i))
            `DBG(("v = %b, length = %0d", obj.v, obj.length))

            // Validate that the constraint is indeed working
            if (obj.length != obj.count_ones(obj.v)) $fatal("Constraint violated: length != count_ones(v)");
        end

        `DBG(("Functions in constraints test passed."))
        `TEST_PASS
    end
endmodule
