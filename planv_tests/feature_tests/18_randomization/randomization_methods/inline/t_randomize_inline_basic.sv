// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: randomize() with inline constraints

`include "test_utils.svh"

class SimpleSum;
    rand bit [7:0] x, y, z;
    constraint c { z == x + y; }

    function bit check();
        if (!(z == x + y)) begin
            `DBG(("Error: z = %0d does not equal x + y (%0d + %0d)", z, x, y))
            return 0;
        end
        return 1;
    endfunction
endclass

task InlineConstraintDemo(SimpleSum p);
    int success;
    success = p.randomize() with { x < y; };  // Inline constraint added to existing constraint block
    if (success) begin
        `DBG(("Randomization successful: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z))
        if (!p.check()) $stop;
    end else begin
        `DBG(("Randomization failed."))
        $stop;
    end
endtask

module t_randomize_inline_basic;
    SimpleSum p = new();

    initial begin
        InlineConstraintDemo(p);
        `TEST_PASS
    end
endmodule
