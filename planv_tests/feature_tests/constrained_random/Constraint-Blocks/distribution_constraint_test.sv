/*
    Solver Error
*/

class DistributionConstraintTest;
    rand int value;

    constraint dist_con {
        value dist { [0:9] :/ 25, [10:19] :/ 50, [20:29] :/ 25 };
    }

    function new();
    endfunction
endclass

module distribution_constraint_test;
    DistributionConstraintTest dct;
    initial begin
        dct = new();
        repeat(10) begin
            if (!dct.randomize()) $error("Randomization failed");
            $display("value: %0d", dct.value);
        end
        $finish;
    end
endmodule