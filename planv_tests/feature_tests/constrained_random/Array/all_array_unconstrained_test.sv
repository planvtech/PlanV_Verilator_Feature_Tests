// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class unconstrained_packed_array_test;

    rand bit [3:0] [2:0] [15:0] packed_array;

    function new();
      packed_array = '{default: '{default: '{default: 'h0}}};
    endfunction

    function void display();
      $display("Packed Array:");
      foreach (packed_array[i, j, k]) begin
        $display("packed_array[%0d][%0d][%0d] = %b", i, j, k, packed_array[i][j][k]);
      end
    endfunction

endclass

class unconstrained_unpacked_array_test;

  rand bit unpacked_array_1d [15];
  rand bit unpacked_array_2d [3][5];
  rand bit unpacked_array_3d [3][3][5];
  rand bit [2:0] [15:0] mixed_unpacked_array [3][5];

  function new();
    unpacked_array_1d = '{default: 'h0};
    unpacked_array_2d = '{default: '{default: 'h0}};
    unpacked_array_3d = '{default: '{default: '{default: 'h0}}};
    mixed_unpacked_array = '{default: '{default: '{default: 'h0}}};
  endfunction

  function void display();
    $display("Unpacked Array 1D:");
    foreach (unpacked_array_1d[i]) begin
      $display("unpacked_array_1d[%0d] = %b", i, unpacked_array_1d[i]);
    end

    $display("Unpacked Array 2D:");
    foreach (unpacked_array_2d[i, j]) begin
      $display("unpacked_array_2d[%0d][%0d] = %b", i, j, unpacked_array_2d[i][j]);
    end

    $display("Unpacked Array 3D:");
    foreach (unpacked_array_3d[i, j, k]) begin
      $display("unpacked_array_3d[%0d][%0d][%0d] = %b", i, j, k, unpacked_array_3d[i][j][k]);
    end

    $display("Mixed Unpacked Array:");
    foreach (mixed_unpacked_array[i, j]) begin
      $display("mixed_unpacked_array[%0d][%0d] = %b", i, j, mixed_unpacked_array[i][j]);
    end
  endfunction

endclass

class unconstrained_dynamic_array_test;

  rand int dynamic_array_1d[];
  rand int dynamic_array_2d[][];
  rand int dynamic_array_3d[][][];

  function new();
    dynamic_array_1d = new[5];
    dynamic_array_2d = new[3];
    foreach (dynamic_array_2d[i]) begin
      dynamic_array_2d[i] = new[3];
    end
    dynamic_array_3d = new[3];
    foreach (dynamic_array_3d[i]) begin
      dynamic_array_3d[i] = new[3];
    end
    foreach (dynamic_array_3d[i, j]) begin
      dynamic_array_3d[i][j] = new[3];
    end
  endfunction

  function void display();
    $display("Dynamic Array 1D:");
    foreach (dynamic_array_1d[i]) begin
      $display("dynamic_array_1d[%0d] = %d", i, dynamic_array_1d[i]);
    end

    $display("Dynamic Array 2D:");
    foreach (dynamic_array_2d[i, j]) begin
      $display("dynamic_array_2d[%0d][%0d] = %d", i, j, dynamic_array_2d[i][j]);
    end

    $display("Dynamic Array 3D:");
    foreach (dynamic_array_3d[i, j, k]) begin
      $display("dynamic_array_3d[%0d][%0d][%0d] = %d", i, j, k, dynamic_array_3d[i][j][k]);
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

  function void display();
    $display("Struct with Array:");
    foreach (struct_with_array.byte_array[i]) begin
      $display("struct_with_array.byte_array[%0d] = %h", i, struct_with_array.byte_array[i]);
    end
  endfunction

endclass

class unconstrained_associative_array_test;

  rand int associative_array_1d[string];
  rand int associative_array_2d[string][string];

  function new();
   associative_array_1d = '{"Peter":20, "Paul":22, "Mary":23};
   associative_array_2d = '{"Peter":'{"age":20, "math":90},
                            "Paul":'{"age":22, "math":98}, 
                            "Mary":'{"age":23, "math":88}};
  endfunction

  function void display();
    $display("Associative Array 1D:");
    foreach (associative_array_1d[key]) begin
      $display("associative_array_1d[%s] = %d", key, associative_array_1d[key]);
    end
   
    $display("Associative Array 2D:");
    foreach (associative_array_2d[key1, key2]) begin
      $display("associative_array_2d[%s][%s] = %d", key1, key2, associative_array_2d[key1][key2]);
    end
  endfunction

endclass

class unconstrained_queue_test;

  rand int queue_array_1d[$];
  rand int queue_array_2d[$][$];

  function new();
    queue_array_1d = {1, 2, 3};
    //queue_array_2d = '{'{1, 2},
    //                   '{3, 4, 5}}; // Work in verilator, error in vsim
    queue_array_2d = {};
    queue_array_2d[0] = {1, 2};
    queue_array_2d[1] = {3, 4, 5};
    queue_array_2d[2] = {6};
  endfunction

  function void display();
    $display("Queue Array 1D:");
    foreach (queue_array_1d[i]) begin
      $display("queue_array_1d[%0d] = %d", i, queue_array_1d[i]);
    end
    $display("Queue Array 2D:");
    foreach (queue_array_2d[i, j]) begin
      $display("queue_array_2d[%0d][%0d] = %d", i, j, queue_array_2d[i][j]);
    end
  endfunction

endclass

module all_array_unconstrained_test;
  unconstrained_packed_array_test  packed_class;
  unconstrained_unpacked_array_test unpacked_class;
  unconstrained_dynamic_array_test dynamic_class;
  unconstrained_struct_with_array_test struct_with_array_class;
  unconstrained_associative_array_test associative_array_class;
  unconstrained_queue_test queue_class;

  int success;

  initial begin
    // Test 1: Packed Array Unconstrained Randomize and Display Test
    packed_class = new();
    void'(packed_class.randomize());
    packed_class.display();

    // Test 2: Unpacked Array Unconstrained Randomize and Display Test
    unpacked_class = new();
    void'(unpacked_class.randomize());
    unpacked_class.display();

    // Test 3: Dynamic Array Unconstrained Randomize and Display Test
    dynamic_class = new();
    void'(dynamic_class.randomize());
    dynamic_class.display();

    // Test 4: Struct Containing Array Randomize and Display Test
    struct_with_array_class = new();
    void'(struct_with_array_class.randomize());
    struct_with_array_class.display();

    // Test 5: Associative Array Unconstrained Randomize and Display Test
    associative_array_class = new();
    associative_array_class.display();
    void'(associative_array_class.randomize());
    associative_array_class.display();

    // Test 6: Queue Unconstrained Randomize and Display Test
    queue_class = new();
    queue_class.display();
    success = queue_class.randomize();
    $display(success);
    queue_class.display();

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
