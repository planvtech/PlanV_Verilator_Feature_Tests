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

    constraint enum_constraint {
        enum_value inside {ENUM_ONE, ENUM_TWO, ENUM_THREE};
    }
    constraint 32_bit_constraint {
        (random_32_bit && 32'hFFFF0000) == 32'hABCD0000;
    }
    constraint single_bit_constraint {
        single_bit == 1;
    }

    function new();
        enum_value = ENUM_ONE;
    endfunction
endclass

module basic_rand_constrained_test;
    BasicRandTest rand_test;
    initial begin
        rand_test = new();
        repeat(10) begin
            if (!rand_test.randomize()) $error("Randomization failed");
            $display("enum_value: %0d, random_32_bit: %h, single_bit: %b", rand_test.enum_value, rand_test.random_32_bit, rand_test.single_bit);
        end
        $finish;
    end
endmodule
