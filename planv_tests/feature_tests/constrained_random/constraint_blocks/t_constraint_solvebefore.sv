// DESCRIPTION: PlanV Verilator Solve Before Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class SolveBeforeConstraintTest;
    rand bit [3:0] a;
    rand bit [3:0] b;

    constraint solve_before_con {
        solve a before b;
    }

    function new();
    endfunction
endclass

module t_constraint_solvebefore;
    SolveBeforeConstraintTest sbct;

    initial begin
        sbct = new();
        repeat(10) begin
            if (!sbct.randomize()) $error("Randomization failed");
            $display("a: %0d, b: %0d", sbct.a, sbct.b);
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
