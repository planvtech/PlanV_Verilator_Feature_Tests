// DESCRIPTION: PlanV Verilator Constrained Randomization Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

typedef enum bit [15:0] {
    ENUM_ONE = 3,
    ENUM_TWO = 5,
    ENUM_THREE = 8,
    ENUM_FOUR = 13
} ENUM;

class BasicRandTest;
    rand ENUM enum_value;
    rand bit [31:0] random_32_bit;
    rand bit single_bit;

    // Constraints
    constraint enum_constraint {
        enum_value inside {ENUM_ONE, ENUM_TWO, ENUM_THREE};
    }
    constraint random_32_bit_constraint {
        (random_32_bit & 32'hFFFF0000) == 32'hABCD0000;
    }
    constraint single_bit_constraint {
        single_bit == 1;
    }

    function new();
        enum_value = ENUM_ONE;
    endfunction

    // Self-check function
    function void check();
        if (!(enum_value inside {ENUM_ONE, ENUM_TWO, ENUM_THREE})) begin
            $display("Error: enum_value = %0d is out of bounds", enum_value);
            $stop;
        end
        if (!((random_32_bit & 32'hFFFF0000) == 32'hABCD0000)) begin
            $display("Error: random_32_bit = %h does not satisfy the constraint", random_32_bit);
            $stop;
        end
        if (single_bit != 1) begin
            $display("Error: single_bit = %b does not equal 1", single_bit);
            $stop;
        end
        $display("All constraints validated successfully.");
    endfunction
endclass

module t_constraint_basic_types;
    BasicRandTest rand_test;

    initial begin
        rand_test = new();
        repeat(10) begin
            if (!rand_test.randomize()) $error("Randomization failed");

            // Self-check to validate constraints after randomization
            rand_test.check();

            $display("enum_value: %0d, random_32_bit: %h, single_bit: %b", 
                     rand_test.enum_value, rand_test.random_32_bit, rand_test.single_bit);
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
