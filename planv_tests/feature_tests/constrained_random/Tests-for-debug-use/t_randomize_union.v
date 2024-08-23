typedef union packed {
    int int_value;
    bit [31:0] bits;
} SimpleUnion;

typedef struct packed {
    rand bit [3:0] field_a;
    rand bit [7:0] field_b;
} PackedStruct;

typedef union packed {
    PackedStruct struct_fields;
    bit [11:0] raw_bits;
} StructInUnion;

typedef union packed {
    StructInUnion inner_union;
    bit [15:0] full_bits;
} UnionInUnion;

// SimpleUnion Constrained Test Class
class SimpleUnionConstrainedTest;
    rand SimpleUnion union_instance;

    function new();
        union_instance.bits = 32'b0;
    endfunction

    constraint union_constraint {
        union_instance.bits[11:0] inside {[0:4095]};
    }
endclass

// SimpleUnion Unconstrained Test Class
class SimpleUnionUnconstrainedTest;
    rand SimpleUnion union_instance;

    function new();
        union_instance.bits = 32'b0;
    endfunction
endclass

// StructInUnion Constrained Test Class
class StructInUnionConstrainedTest;
    rand StructInUnion union_instance;

    function new();
        union_instance.raw_bits = 12'b0;
    endfunction

    constraint union_constraint {
        union_instance.raw_bits inside {[0:4095]};
    }
endclass

// StructInUnion Unconstrained Test Class
class StructInUnionUnconstrainedTest;
    rand StructInUnion union_instance;

    function new();
        union_instance.raw_bits = 12'b0;
    endfunction
endclass

// UnionInUnion Constrained Test Class
class UnionInUnionConstrainedTest;
    rand UnionInUnion union_instance;

    function new();
        union_instance.full_bits = 16'b0;
    endfunction

    constraint union_constraint {
        union_instance.full_bits inside {[0:65535]};
    }
endclass

// UnionInUnion Unconstrained Test Class
class UnionInUnionUnconstrainedTest;
    rand UnionInUnion union_instance;

    function new();
        union_instance.full_bits = 16'b0;
    endfunction
endclass

// Top-Level Test Module
module t_randomize_union;

    // Instances of each test class
    SimpleUnionConstrainedTest test_simple_union_constrained;
    SimpleUnionUnconstrainedTest test_simple_union_unconstrained;
    StructInUnionConstrainedTest test_struct_in_union_constrained;
    StructInUnionUnconstrainedTest test_struct_in_union_unconstrained;
    UnionInUnionConstrainedTest test_union_in_union_constrained;
    UnionInUnionUnconstrainedTest test_union_in_union_unconstrained;

    initial begin
        // Test 1: SimpleUnion Constrained Test
        test_simple_union_constrained = new();
        $display("\n--- Test 1: SimpleUnion Constrained Test ---");
        repeat(10) begin
            if (!test_simple_union_constrained.randomize()) $error("Randomization failed");
            $display("SimpleUnion (Constrained): int_value: %d, bits: %b", test_simple_union_constrained.union_instance.int_value, test_simple_union_constrained.union_instance.bits);
        end

        // Test 2: SimpleUnion Unconstrained Test
        test_simple_union_unconstrained = new();
        $display("\n--- Test 2: SimpleUnion Unconstrained Test ---");
        repeat(10) begin
            if (!test_simple_union_unconstrained.randomize()) $error("Randomization failed");
            $display("SimpleUnion (Unconstrained): int_value: %d, bits: %b", test_simple_union_unconstrained.union_instance.int_value, test_simple_union_unconstrained.union_instance.bits);
        end

        // Test 3: StructInUnion Constrained Test
        test_struct_in_union_constrained = new();
        $display("\n--- Test 3: StructInUnion Constrained Test ---");
        repeat(10) begin
            if (!test_struct_in_union_constrained.randomize()) $error("Randomization failed");
            $display("StructInUnion (Constrained): a: %b, b: %b, raw_bits: %b", test_struct_in_union_constrained.union_instance.struct_fields.field_a, test_struct_in_union_constrained.union_instance.struct_fields.field_b, test_struct_in_union_constrained.union_instance.raw_bits);
        end

        // Test 4: StructInUnion Unconstrained Test
        test_struct_in_union_unconstrained = new();
        $display("\n--- Test 4: StructInUnion Unconstrained Test ---");
        repeat(10) begin
            if (!test_struct_in_union_unconstrained.randomize()) $error("Randomization failed");
            $display("StructInUnion (Unconstrained): a: %b, b: %b, raw_bits: %b", test_struct_in_union_unconstrained.union_instance.struct_fields.field_a, test_struct_in_union_unconstrained.union_instance.struct_fields.field_b, test_struct_in_union_unconstrained.union_instance.raw_bits);
        end

        // Test 5: UnionInUnion Constrained Test
        test_union_in_union_constrained = new();
        $display("\n--- Test 5: UnionInUnion Constrained Test ---");
        repeat(10) begin
            if (!test_union_in_union_constrained.randomize()) $error("Randomization failed");
            $display("UnionInUnion (Constrained): raw_data: %b, a: %b, b: %b", test_union_in_union_constrained.union_instance.full_bits, test_union_in_union_constrained.union_instance.inner_union.struct_fields.field_a, test_union_in_union_constrained.union_instance.inner_union.struct_fields.field_b);
        end

        // Test 6: UnionInUnion Unconstrained Test
        test_union_in_union_unconstrained = new();
        $display("\n--- Test 6: UnionInUnion Unconstrained Test ---");
        repeat(10) begin
            if (!test_union_in_union_unconstrained.randomize()) $error("Randomization failed");
            $display("UnionInUnion (Unconstrained): raw_data: %b, a: %b, b: %b", test_union_in_union_unconstrained.union_instance.full_bits, test_union_in_union_unconstrained.union_instance.inner_union.struct_fields.field_a, test_union_in_union_unconstrained.union_instance.inner_union.struct_fields.field_b);
        end

        $finish;
    end

endmodule