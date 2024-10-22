// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

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
      $display("Error: Randomization failed for %s", `"field"`); \
      $stop; \
   end \
end

typedef union packed {
    int int_value;
    bit [31:0] bits;
} PackedUnion;

class PackedUnionTest;
    rand PackedUnion my_union;

    function new();
        my_union.int_value = 0;
    endfunction

    // Self-check function using check_rand
    function void check();
        `check_rand(this, my_union.int_value);
        `check_rand(this, my_union.bits);
    endfunction
endclass

module t_rand_union;
    PackedUnionTest union_test;

    initial begin
        union_test = new();
        repeat(10) begin
            if (!union_test.randomize()) $error("Randomization failed");

            // Self-check to validate randomization
            union_test.check();

            $display("int_value: %0d, bits: %h", union_test.my_union.int_value, union_test.my_union.bits);
        end

        // Successful execution marker
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
