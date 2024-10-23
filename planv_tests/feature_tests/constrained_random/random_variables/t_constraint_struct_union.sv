// DESCRIPTION: PlanV Verilator Constrained Randomization Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

typedef struct packed {
    bit [3:0] a;
    bit [7:0] b;
} PackedStruct;

typedef union packed {
    PackedStruct s;
    bit [11:0] raw_bits;
} PackedUnion;

typedef union packed {
    PackedUnion u;
    bit [11:0] raw_bits;
} InnerPackedUnion;

typedef union packed {
    InnerPackedUnion u1;
    bit [11:0] raw_data;
} OuterPackedUnion;

class StructUnionTest;
    rand PackedStruct my_struct;
    rand PackedUnion my_union;
    rand InnerPackedUnion my_inner_union;
    rand OuterPackedUnion my_outer_union;

    function new();
        my_struct.a = 4'b0000;
        my_struct.b = 8'h00;
        my_union.raw_bits = 12'b0;
        my_inner_union.u.s.a = 4'b0000;
        my_inner_union.u.s.b = 12'h000;
        my_outer_union.raw_data = 16'b0;
    endfunction

    // Constraints for packed struct
    constraint struct_constraint {
        my_struct.a inside {[0:15]};
        my_struct.b inside {[0:255]};
    }

    // Constraints for packed union
    constraint union_constraint {
        my_union.raw_bits inside {[0:4095]};
    }

    // Constraints for inner union
    constraint inner_union_constraint {
        my_inner_union.raw_bits inside {[0:65535]};
    }

    // Constraints for outer union
    constraint outer_union_constraint {
        my_outer_union.raw_data inside {[0:65535]};
    }

    // Self-check function
    function void check();
        if (!(my_struct.a inside {[0:15]})) begin
            $display("Error: my_struct.a = %b is out of bounds", my_struct.a);
            $stop;
        end
        if (!(my_struct.b inside {[0:255]})) begin
            $display("Error: my_struct.b = %b is out of bounds", my_struct.b);
            $stop;
        end
        if (!(my_union.raw_bits inside {[0:4095]})) begin
            $display("Error: my_union.raw_bits = %b is out of bounds", my_union.raw_bits);
            $stop;
        end
        if (!(my_inner_union.raw_bits inside {[0:65535]})) begin
            $display("Error: my_inner_union.raw_bits = %b is out of bounds", my_inner_union.raw_bits);
            $stop;
        end
        if (!(my_outer_union.raw_data inside {[0:65535]})) begin
            $display("Error: my_outer_union.raw_data = %b is out of bounds", my_outer_union.raw_data);
            $stop;
        end
        $display("All constraints validated successfully.");
    endfunction
endclass

module t_constraint_struct_union;
    StructUnionTest test;

    initial begin
        test = new();
        repeat(10) begin
            if (!test.randomize()) $error("Randomization failed");

            // Self-check to validate constraints after randomization
            test.check();

            // Display values after randomization
            $display("PackedStruct: a: %b, b: %b", test.my_struct.a, test.my_struct.b);
            $display("Union: raw_bits: %b, s: %b", test.my_union.raw_bits, test.my_union.s);
            $display("Inner Union: a: %b, b: %b, raw_bits: %b", test.my_inner_union.u.s.a, test.my_inner_union.u.s.b, test.my_inner_union.raw_bits);
            $display("Outer Union: raw_data: %b", test.my_outer_union.raw_data);
            $display("***************************");
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
