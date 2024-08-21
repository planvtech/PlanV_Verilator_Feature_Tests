typedef union packed {
    int int_value;
    bit [31:0] bits;
} PackedUnion;

typedef struct packed {
    rand bit [7:0] byte_value;
    rand int int_value;
} PackedStruct;

class PackedStructAndUnionTest;
    rand PackedStruct my_struct;
    rand PackedUnion my_union;

    function new();
        my_struct.byte_value = 8'hA0;
        my_union.int_value = 0;
    endfunction

    // Constraint block
    constraint struct_constraint {
        my_struct.byte_value == 8'hA0;    // Keep byte_value fixed at 8'hA0
        my_struct.int_value inside {[0:100]};  // Constrain int_value to be between 0 and 100
    }
    constraint union_constraint {
        my_union.int_value inside {[0:100]};  // Constrain int_value to be between 0 and 100
        // Since bits and int_value share the same memory, this constraint indirectly constrains bits as well
    }

endclass

module packed_UnionStruct_constrained_test;
    PackedStructAndUnionTest test;
    initial begin
        test = new();
        repeat(10) begin
            if (!test.randomize()) $error("Randomization failed");
            $display("Struct:  byte_value: %h, int_value: %0d", test.my_struct.byte_value, test.my_struct.int_value);
            $display("Union :  bits: %d, int_value: %0d", test.my_union.bits, test.my_union.int_value);
        end
        $finish;
    end
endmodule