// DESCRIPTION: PlanV Verilator Uniqueness Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class UniquenessConstraintTest;
    rand bit [7:0] value1;
    rand bit [7:0] value2;
    rand bit [7:0] value3;

    constraint unique_con {
        unique {value1, value2, value3}; // Ensure all values are unique
    }

    function new();
    endfunction
endclass

module t_constraint_unique;
    UniquenessConstraintTest uct;

    initial begin
        uct = new();
        repeat(10) begin
            if (!uct.randomize()) $error("Randomization failed");
            $display("value1: %0d, value2: %0d, value3: %0d", uct.value1, uct.value2, uct.value3);
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
