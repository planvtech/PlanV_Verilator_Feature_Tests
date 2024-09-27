// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

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
   if (ok != 1) $stop; \
end

class unconstrained_packed_array_test;

    rand bit [3:0] [2:0] [15:0] packed_array;
    function new();
      packed_array = '{default: '{default: '{default: 'h0}}};
    endfunction

    function void check_randomization();
      `check_rand(this, this.packed_array)
    endfunction

endclass

class unconstrained_unpacked_array_test;

  rand bit [2:0] [15:0] unpacked_array [3][5];
  function new();
    unpacked_array = '{ '{default: '{default: 'h0}},
                        '{default: '{default: 'h1}},
                        '{default: '{default: 'h2}}};
  endfunction

  function void check_randomization();
    foreach (unpacked_array[i]) begin
      foreach (unpacked_array[i][j]) begin
        // At the innermost packed level, invoke check_rand
        `check_rand(this, this.unpacked_array[i][j])
      end
    end
  endfunction

endclass

class unconstrained_dynamic_array_test;

  rand int dynamic_array_1d[];
  rand int dynamic_array_2d[][];

  function new();
    // Initialize 1D dynamic array
    dynamic_array_1d = new[5];
    foreach(dynamic_array_1d[i]) begin
      dynamic_array_1d[i] = 'h0 + i;
    end

    // Initialize 2D dynamic array
    dynamic_array_2d = new[3];
    foreach(dynamic_array_2d[i]) begin
      dynamic_array_2d[i] = new[3];
      foreach(dynamic_array_2d[i][j]) begin
        dynamic_array_2d[i][j] = 'h0 + i + j;
      end
    end
  endfunction

  function void check_randomization();
    foreach (dynamic_array_1d[i]) begin
      `check_rand(this, dynamic_array_1d[i])
    end
    foreach (dynamic_array_2d[i]) begin
      foreach (dynamic_array_2d[i][j]) begin
        `check_rand(this, dynamic_array_2d[i][j])
      end
    end
  endfunction

endclass

class unconstrained_struct_with_array_test;

  typedef struct {
    rand bit [7:0] byte_array[4];
  } struct_with_array_t;

  rand struct_with_array_t struct_with_array;

  function new();
    struct_with_array = '{'{default: 'h0}};
  endfunction

  function void check_randomization();
    foreach (struct_with_array.byte_array[i]) begin
      `check_rand(this, struct_with_array.byte_array[i])
    end
  endfunction

endclass

module array_unconstrained_test;
  unconstrained_packed_array_test  packed_class;
  unconstrained_unpacked_array_test unpacked_class;
  unconstrained_dynamic_array_test dynamic_class;
  unconstrained_struct_with_array_test struct_with_array_class;

  initial begin
    // Test 1: Packed Array Unconstrained Constrained Test
    packed_class = new();
    repeat(2) begin
      packed_class.check_randomization();
      // Display the randomized packed array
      $display("Randomized Packed Array:");
      foreach (packed_class.packed_array[i, j, k]) begin
        $display("packed_array[%0d][%0d][%0d] = %0h", i, j, k, packed_class.packed_array[i][j][k]);
      end
    end

    // Test 2: Unpacked Array Unconstrained Constrained Test
    unpacked_class = new();
    repeat(2) begin
      unpacked_class.check_randomization();
      // Display the randomized unpacked array
      $display("Randomized Unpacked Array:");
      foreach (unpacked_class.unpacked_array[i, j]) begin
        $display("unpacked_array[%0d][%0d] = %0h", i, j, unpacked_class.unpacked_array[i][j]);
      end
    end

    // Test 3: Dynamic Array Unconstrained Constrained Test
    dynamic_class = new();
    repeat(2) begin
      dynamic_class.check_randomization();
      // Display the randomized dynamic 1D array
      $display("Randomized Dynamic 1D Array:");
      foreach (dynamic_class.dynamic_array_1d[i]) begin
        $display("dynamic_array_1d[%0d] = %0d", i, dynamic_class.dynamic_array_1d[i]);
      end

      // Display the randomized dynamic 2D array
      $display("Randomized Dynamic 2D Array:");
      foreach (dynamic_class.dynamic_array_2d[i, j]) begin
        $display("dynamic_array_2d[%0d][%0d] = %0d", i, j, dynamic_class.dynamic_array_2d[i][j]);
      end
    end

    // Test 4: Struct Containing Array Test
    struct_with_array_class = new();
    repeat(2) begin
      struct_with_array_class.check_randomization();
      // Display the randomized struct with array
      $display("Randomized Struct Array:");
      foreach (struct_with_array_class.struct_with_array.byte_array[i]) begin
        $display("struct_with_array.byte_array[%0d] = %0h", i, struct_with_array_class.struct_with_array.byte_array[i]);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
