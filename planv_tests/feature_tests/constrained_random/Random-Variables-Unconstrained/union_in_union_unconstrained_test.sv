typedef struct packed {
    rand bit [3:0] a;
    rand bit [11:0] b;
} PackedStruct;

typedef union packed {
    PackedStruct s;
    bit [15:0] raw_bits;
} InnerPackedUnion;

typedef union packed {
    InnerPackedUnion u1;
    bit [15:0] raw_data;
} OuterPackedUnion;

class UnionInUnionTest;
    rand OuterPackedUnion my_outer_union;

    function new();
        my_outer_union.raw_data = 16'b0;
    endfunction

endclass

module union_in_union_unconstrained_test;
    UnionInUnionTest test;

    initial begin
        test = new();
        repeat(10) begin
            if (!test.randomize()) $error("Randomization failed");
            $display("Inner Union Struct: a: %b, b: %b, raw_bits: %b", test.my_outer_union.u1.s.a, test.my_outer_union.u1.s.b, test.my_outer_union.u1.raw_bits);
            $display("Outer Union: raw_data: %b", test.my_outer_union.raw_data);
        end
        $finish;
    end
endmodule
