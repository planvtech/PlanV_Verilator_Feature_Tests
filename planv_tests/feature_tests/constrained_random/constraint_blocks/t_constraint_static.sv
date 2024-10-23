// DESCRIPTION: PlanV Verilator Static Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class C;
    rand bit [7:0] a, b, c;

    static constraint sum_constraint { a + b == c; }

    function new();
    endfunction
endclass

module t_constraint_static;
    C obj1 = new();
    C obj2 = new();
    int i;

    initial begin
        // Disable the static constraint for all instances
        C::sum_constraint.constraint_mode(0);

        for (i = 0; i < 100; i++) begin
            if (!obj1.randomize()) $fatal("Randomization failed for obj1.");
            if (!obj2.randomize()) $fatal("Randomization failed for obj2.");

            // Display the values
            $display("Randomization %0d:", i);
            $display("obj1: a = %0d, b = %0d, c = %0d", obj1.a, obj1.b, obj1.c);
            $display("obj2: a = %0d, b = %0d, c = %0d", obj2.a, obj2.b, obj2.c);

            // Validate that the constraint is indeed turned off
            if (obj1.a + obj1.b == obj1.c) $fatal("Static constraint should be OFF for obj1.");
            if (obj2.a + obj2.b == obj2.c) $fatal("Static constraint should be OFF for obj2.");
        end

        // Enable the static constraint for all instances
        C::sum_constraint.constraint_mode(1);

        for (i = 0; i < 100; i++) begin
            if (!obj1.randomize()) $fatal("Randomization failed for obj1.");
            if (!obj2.randomize()) $fatal("Randomization failed for obj2.");

            // Display the values
            $display("Randomization %0d:", i);
            $display("obj1: a = %0d, b = %0d, c = %0d", obj1.a, obj1.b, obj1.c);
            $display("obj2: a = %0d, b = %0d, c = %0d", obj2.a, obj2.b, obj2.c);

            // Validate that the constraint is now turned on
            if (obj1.a + obj1.b != obj1.c) $fatal("Static constraint should be ON for obj1.");
            if (obj2.a + obj2.b != obj2.c) $fatal("Static constraint should be ON for obj2.");
        end

        $display("Static constraint test passed.");
        $finish;
    end
endmodule