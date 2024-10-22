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

typedef struct packed {
    rand bit [7:0] byte_value;
    rand int int_value;
} PackedStruct;

typedef struct {
    rand logic [7:0] byte_value;
    rand int int_value;
} UnpackedStruct;

class StructTest;
    rand PackedStruct packed_struct;
    rand UnpackedStruct unpacked_struct;

    function new();
        packed_struct.byte_value = 8'hA0;
        unpacked_struct.byte_value = 8'hF0;
    endfunction

    // Self-check function using check_rand
    function void check();
        `check_rand(this, packed_struct.byte_value);
        `check_rand(this, packed_struct.int_value);
        `check_rand(this, unpacked_struct.byte_value);
        `check_rand(this, unpacked_struct.int_value);
    endfunction
endclass

module t_rand_struct;
    StructTest struct_test;

    initial begin
        struct_test = new();
        repeat(10) begin
            if (!struct_test.randomize()) $error("Randomization failed");

            // Self-check to validate randomization
            struct_test.check();

            $display("Packed Struct - byte_value: %h, int_value: %0d", struct_test.packed_struct.byte_value, struct_test.packed_struct.int_value);
            $display("Unpacked Struct - byte_value: %h, int_value: %0d", struct_test.unpacked_struct.byte_value, struct_test.unpacked_struct.int_value);
        end

        // Successful execution marker
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
