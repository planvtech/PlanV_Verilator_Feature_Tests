typedef struct packed {
    rand bit [3:0] a;
    rand bit [7:0] b;
} PackedStruct;

typedef union packed {
    PackedStruct s;
    bit [11:0] raw_bits;
} PackedUnion;

class StructInUnionTest;
    rand PackedUnion my_union;

    function new();
        my_union.raw_bits = 12'b0;
    endfunction

endclass

module struct_in_union_unconstrained_test;
    StructInUnionTest test;

    initial begin
        test = new();
        repeat(10) begin
            if (!test.randomize()) $error("Randomization failed");
            $display("Struct: a: %b, b: %b", test.my_union.s.a, test.my_union.s.b);
            $display("Union : raw_bits: %b", test.my_union.raw_bits);
        end
        $finish;
    end
endmodule
