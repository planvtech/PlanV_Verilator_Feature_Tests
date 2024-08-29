typedef struct packed {
    rand bit [3:0] a;
    rand bit [7:0] b;
} PackedStruct;

typedef union packed {
    PackedStruct s;
    bit [11:0] raw_bits;
} PackedUnion;

class StructInUnionTest;
    rand PackedStruct my_struct;
    rand PackedUnion my_union;

    function new();
        my_struct.a = 4'b0000;
        my_struct.b = 8'h00;
        my_union.raw_bits = 12'b0;
    endfunction

    constraint struct_constraint {
        my_struct.a inside {[0:15]};
        my_struct.b inside {[0:255]};
    }

    constraint union_constraint {
        my_union.raw_bits inside {[0:4095]};
    }

endclass

module struct_in_union_constrained_test;
    StructInUnionTest test;

    initial begin
        test = new();
        repeat(10) begin
            if (!test.randomize()) $error("Randomization failed");
            $display("Struct: a: %b, b: %b", test.my_struct.a, test.my_struct.b);
            $display("Union : raw_bits: %b, s: %b", test.my_union.raw_bits, test.my_union.s);
        end
        $finish;
    end
endmodule