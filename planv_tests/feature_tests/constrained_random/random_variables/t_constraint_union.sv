// DESCRIPTION: PlanV Verilator Union Constrained Randomization Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

typedef union packed {
    int int_value;
    bit [31:0] bits;
} PackedUnion;

class PackedUnionTest;
    rand PackedUnion my_union;

    function new();
        my_union.int_value = 0;
    endfunction

    constraint union_constraint {
        my_union.int_value inside {[0:100]};  // Constrain int_value to be between 0 and 100
    }

    // Self-check function
    function void check();
        if (!(my_union.int_value inside {[0:100]})) begin
            $display("Error: my_union.int_value = %0d is out of bounds", my_union.int_value);
            $stop;
        end
        $display("PackedUnion constraints validated successfully.");
    endfunction
endclass

module t_constraint_union;
    PackedUnionTest union_test;

    initial begin
        union_test = new();
        repeat(10) begin
            if (!union_test.randomize()) $error("Randomization failed");
            
            // Self-check to validate constraints after randomization
            union_test.check();

            // Displaying the values after randomization
            $display("int_value: %0d, bits: %h", union_test.my_union.int_value, union_test.my_union.bits);
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
