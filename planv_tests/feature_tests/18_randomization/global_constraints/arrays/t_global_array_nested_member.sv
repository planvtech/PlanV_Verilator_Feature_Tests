// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints on nested member arrays

`include "test_utils.svh"

/* verilator lint_off WIDTHTRUNC */
class Inner;
    rand int x;
    rand int y;
endclass

class Middle;
    rand Inner obj;
    rand Inner arr[3];
endclass

class Outer;
    rand Middle mid;
    rand Middle mid_arr[2];

    function new();
        mid = new;
        mid.obj = new;
        foreach (mid.arr[i]) mid.arr[i] = new;
        foreach (mid_arr[i]) begin
            mid_arr[i] = new;
            mid_arr[i].obj = new;
            foreach (mid_arr[i].arr[j]) mid_arr[i].arr[j] = new;
        end
    endfunction

    // Case 1: Simple nested member access (should work)
    constraint c_simple {
        mid.obj.x == 100;
        mid.obj.y == 101;
    }

    // Case 2: Array indexing in the path (may not work)
    constraint c_array_index {
        mid.arr[0].x == 200;
        mid.arr[0].y == 201;
    }

    // Case 3: Nested array indexing
    constraint c_nested_array {
        mid_arr[0].obj.x == 300;
        mid_arr[0].obj.y == 301;
    }

    // Case 4: Multiple array indices
    constraint c_multi_array {
        mid_arr[1].arr[2].y == 400;
    }
endclass

module t_global_array_nested_member;
    initial begin
        Outer o = new;
        if (o.randomize()) begin
            `DBG(("Case 1 - Simple: mid.obj.x = %0d (expected 100)", o.mid.obj.x))
            `DBG(("Case 1 - Simple: mid.obj.y = %0d (expected 101)", o.mid.obj.y))
            `DBG(("Case 2 - Array[0]: mid.arr[0].x = %0d (expected 200)", o.mid.arr[0].x))
            `DBG(("Case 2 - Array[0]: mid.arr[0].y = %0d (expected 201)", o.mid.arr[0].y))
            `DBG(("Case 3 - Nested[0]: mid_arr[0].obj.x = %0d (expected 300)", o.mid_arr[0].obj.x))
            `DBG(("Case 3 - Nested[0]: mid_arr[0].obj.y = %0d (expected 301)", o.mid_arr[0].obj.y))
            `DBG(("Case 4 - Multi[1][2]: mid_arr[1].arr[2].y = %0d (expected 400)", o.mid_arr[1].arr[2].y))

            // Check results
            if (o.mid.obj.x == 100 && o.mid.obj.y == 101 &&
                o.mid.arr[0].x == 200 && o.mid.arr[0].y == 201 &&
                o.mid_arr[0].obj.x == 300 && o.mid_arr[0].obj.y == 301 &&
                o.mid_arr[1].arr[2].y == 400) begin
                `TEST_PASS
            end else begin
                `DBG(("*-* FAILED *-*"))
                $stop;
            end
        end else begin
            `DBG(("*-* FAILED: randomize() returned 0 *-*"))
            $stop;
        end
    end
endmodule
/* verilator lint_off WIDTHTRUNC */