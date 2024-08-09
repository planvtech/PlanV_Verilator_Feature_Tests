/*
    Known Unsupported Feature Tests due to the lack of support for "extern"
*/

class ExternalConstraintExample;
    rand int x;
    rand int y;

    constraint proto1; // Implicit form
    extern constraint proto2; // Explicit form
endclass

// Constraint for proto1 (implicit form)
constraint ExternalConstraintExample::proto1 {
    x inside {-4, 5, 7};
}

// Constraint for proto2 (explicit form)
constraint ExternalConstraintExample::proto2 {
    y >= 0;
}

module external_constraint_test;
    ExternalConstraintExample ece;
    initial begin
        ece = new();
        repeat(10) begin
            if (!ece.randomize()) $error("Randomization failed");
            $display("x: %0d, y: %0d", ece.x, ece.y);
        end
        $finish;
    end
endmodule
