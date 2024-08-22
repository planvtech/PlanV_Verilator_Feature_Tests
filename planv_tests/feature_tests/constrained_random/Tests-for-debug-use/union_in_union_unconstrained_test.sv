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
    rand InnerPackedUnion my_inner_union;
    rand OuterPackedUnion my_outer_union;

    function new();
        my_inner_union.s.a = 4'b0000;
        my_inner_union.s.b = 12'h000;
        my_outer_union.raw_data = 16'b0;
    endfunction

endclass

module union_in_union_unconstrained_test;
    UnionInUnionTest test;

    initial begin
        test = new();
        repeat(10) begin
            if (!test.randomize()) $error("Randomization failed");
            $display("Inner Union Struct: a: %b, b: %h", test.my_inner_union.s.a, test.my_inner_union.s.b);
            $display("Outer Union: raw_data: %b", test.my_outer_union.raw_data);
        end
        $finish;
    end
endmodule
