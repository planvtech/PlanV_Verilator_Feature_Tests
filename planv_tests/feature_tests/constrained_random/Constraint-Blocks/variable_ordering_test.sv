class B;
    rand bit s;
    rand bit [31:0] d;

    // Constraint to ensure s implies d is 0
    constraint c { s -> d == 0; }

    // Ordering constraint to solve s before d
    constraint order { solve s before d; }

    function new();
    endfunction
endclass

module variable_ordering_test;
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
