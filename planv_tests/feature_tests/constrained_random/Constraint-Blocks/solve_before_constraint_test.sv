class SolveBeforeConstraintTest;
    rand bit [3:0] a;
    rand bit [3:0] b;

    constraint solve_before_con {
        solve a before b;
    }

    function new();
    endfunction
endclass

module solve_before_constraint_test;
    SolveBeforeConstraintTest sbct;
    initial begin
        sbct = new();
        repeat(10) begin
            if (!sbct.randomize()) $error("Randomization failed");
            $display("a: %0d, b: %0d", sbct.a, sbct.b);
        end
        $finish;
    end
endmodule