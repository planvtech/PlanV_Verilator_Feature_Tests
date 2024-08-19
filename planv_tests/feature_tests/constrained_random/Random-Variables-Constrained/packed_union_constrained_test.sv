typedef union packed {
    int int_value;
    bit [31:0] bits;
} PackedUnion;

class PackedUnionTest;
    rand PackedUnion my_union;

    function new();
        my_union.int_value = 0;
    endfunction

    // Constraint block
    constraint union_constraint {
        my_union.int_value inside {[0:100]};  // Constrain int_value to be between 0 and 100
        // Since bits and int_value share the same memory, this constraint indirectly constrains bits as well
    }

endclass

module packed_union_constrained_test;
    PackedUnionTest union_test;
    initial begin
        union_test = new();
        repeat(10) begin
            if (!union_test.randomize()) $error("Randomization failed");
            $display("int_value: %0d, bits: %h", union_test.my_union.int_value, union_test.my_union.bits);
        end
        $finish;
    end
endmodule