// DESCRIPTION: PlanV Verilator External Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class ExternalConstraintExample;
    rand int x;
    rand int y;

    constraint proto1;
    extern constraint proto2; // Explicit form
endclass

constraint ExternalConstraintExample::proto1 {
    x inside {-4, 5, 7};
}

constraint ExternalConstraintExample::proto2 {
    y >= 0;
}

module t_constraint_extern;
    ExternalConstraintExample ece;

    initial begin
        ece = new();
        repeat(10) begin
            if (!ece.randomize()) $error("Randomization failed");
            $display("x: %0d, y: %0d", ece.x, ece.y);
            if (!(ece.x inside {-4, 5, 7})) $stop;
            if (!(ece.y >= 0)) $stop;
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
