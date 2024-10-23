// DESCRIPTION: PlanV Verilator Distribution Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class DistributionConstraintTest;
    rand int value;

    constraint dist_con {
        value dist { [0:9] :/ 25, [10:19] :/ 50, [20:29] :/ 25 };
    }

    function new();
    endfunction
endclass

module t_constraint_dist;
    DistributionConstraintTest dct;

    initial begin
        dct = new();
        repeat(10) begin
            if (!dct.randomize()) $error("Randomization failed");
            $display("value: %0d", dct.value);
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
