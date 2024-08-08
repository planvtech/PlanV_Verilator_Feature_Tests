class ForeachConstraintTest;
    rand bit [7:0] array [4];

    constraint foreach_con {
        foreach (array[i]) {
            array[i] inside {0, 1, 2, 3};
        }
    }

    function new();
    endfunction
endclass

module foreach_simple_constraint_test;
    ForeachConstraintTest fct;
    initial begin
        fct = new();
        repeat(10) begin
            if (!fct.randomize()) $error("Randomization failed");
            $display("array: %p", fct.array);
        end
        $finish;
    end
endmodule