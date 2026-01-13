// DESCRIPTION: PlanV Verilator Basic Data Types Randomization Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) begin \
      $display("Error: Randomization failed for %s", field); \
      $stop; \
   end \
end

typedef enum bit [15:0] {
    ENUM_ONE = 3,
    ENUM_TWO = 5,
    ENUM_THREE = 8,
    ENUM_FOUR = 13
} ENUM;

class BasicRandTest;
    // Randomizable fields with formal names
    rand ENUM enum_selection;
    rand bit [31:0] random_value_32bit;
    rand bit random_single_bit;

    function new();
        enum_selection = ENUM_ONE;
    endfunction

    // Self-check function using check_rand
    function void check();
        `check_rand(this, enum_selection);
        `check_rand(this, random_value_32bit);
        `check_rand(this, random_single_bit);
    endfunction
endclass

module t_rand_basic_types;
    BasicRandTest rand_test;

    initial begin
        rand_test = new();
        repeat(10) begin
            if (!rand_test.randomize()) $error("Randomization failed");
            // Use check_rand to validate the randomization
            rand_test.check();

            $display("enum_selection: %0d, random_value_32bit: %h, random_single_bit: %b", 
                     rand_test.enum_selection, rand_test.random_value_32bit, rand_test.random_single_bit);
        end

        // Successful execution marker
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
