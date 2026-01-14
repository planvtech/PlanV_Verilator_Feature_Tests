// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: rand struct and union randomization

`include "test_utils.svh"

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
      `DBG(("Error: Randomization failed for %s", field)) \
      $stop; \
   end \
end

typedef struct packed {
    bit [3:0] a;
    bit [7:0] b;
} PackedStruct1;

typedef union packed {
    PackedStruct1 s;
    bit [11:0] raw_bits;
} PackedUnion1;

class StructInUnionTest;
    rand PackedUnion1 my_union1;

    function new();
        my_union1.raw_bits = 12'b0;
    endfunction

    // Self-check function using check_rand
    function void check();
        `check_rand(this, my_union1.s.a);
        `check_rand(this, my_union1.s.b);
        `check_rand(this, my_union1.raw_bits);
    endfunction
endclass

typedef struct packed {
    bit [3:0] a;
    bit [11:0] b;
} PackedStruct2;

typedef union packed {
    PackedStruct2 s;
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

    // Self-check function using check_rand
    function void check();
        `check_rand(this, my_outer_union.u1.s.a);
        `check_rand(this, my_outer_union.u1.s.b);
        `check_rand(this, my_outer_union.u1.raw_bits);
        `check_rand(this, my_outer_union.raw_data);
    endfunction
endclass

module t_rand_struct_union_simple;
    StructInUnionTest struct_in_union_test;
    UnionInUnionTest union_in_union_test;

    initial begin
        struct_in_union_test = new();
        repeat(10) begin
            if (!struct_in_union_test.randomize()) $error("Randomization failed");
            struct_in_union_test.check();
            `DBG(("StructInUnionTest - Struct: a: %b, b: %b", struct_in_union_test.my_union1.s.a, struct_in_union_test.my_union1.s.b))
            `DBG(("StructInUnionTest - Union: raw_bits: %b", struct_in_union_test.my_union1.raw_bits))
        end

        union_in_union_test = new();
        repeat(10) begin
            if (!union_in_union_test.randomize()) $error("Randomization failed");
            union_in_union_test.check();
            `DBG(("UnionInUnionTest - Inner Union Struct: a: %b, b: %b, raw_bits: %b",
                     union_in_union_test.my_outer_union.u1.s.a,
                     union_in_union_test.my_outer_union.u1.s.b,
                     union_in_union_test.my_outer_union.u1.raw_bits))
            `DBG(("UnionInUnionTest - Outer Union: raw_data: %b", union_in_union_test.my_outer_union.raw_data))
        end

        // Successful execution marker
        `TEST_PASS
    end
endmodule
