// DESCRIPTION: PlanV Verilator Inline Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class SimpleSum;
    rand bit [7:0] x, y, z;
    constraint c { z == x + y; }

    // Self-check function to validate constraints
    function bit check();
        if (!(z == x + y)) begin
            $display("Error: z = %0d does not equal x + y (%0d + %0d)", z, x, y);
            return 0;
        end
        return 1;
    endfunction
endclass

task InlineConstraintDemo(SimpleSum p);
    int success;
    success = p.randomize() with { x < y; };  // Inline constraint for x < y
    if (success) begin
        $display("Randomization successful: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
        if (!p.check()) $stop;
        $display("Randomization failed.");
    end
endtask

module t_constraint_with;
    SimpleSum p = new();

    initial begin
        InlineConstraintDemo(p);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
