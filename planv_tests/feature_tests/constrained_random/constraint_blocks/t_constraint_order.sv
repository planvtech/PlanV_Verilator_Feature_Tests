// DESCRIPTION: PlanV Verilator Variable Ordering Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class B;
    rand bit s;
    rand bit [31:0] d;

    constraint c { s -> d == 0; }        // Ensure if s is true, d must be 0
    constraint order { solve s before d; } // Solve s before d

    function new();
    endfunction
endclass

module t_constraint_order;
    B obj = new();
    int i;

    initial begin
        for (i = 0; i < 100; i++) begin
            if (!obj.randomize()) $fatal("Randomization failed.");

            // Display the values of s and d
            $display("Randomization %0d: s = %0b, d = %0d", i, obj.s, obj.d);

            // Validate constraints
            if (obj.s && obj.d != 0) $fatal("Constraint violated: s = %0b, d = %0d", obj.s, obj.d);
        end

        $display("Variable ordering test passed.");
        $finish;
    end
endmodule
