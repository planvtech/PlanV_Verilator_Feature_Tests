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
      $display("Error: Randomization failed for %s", field); \
      $stop; \
   end \
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
  rand int unpacked_array1 [9:3][4:8];
  rand int unpacked_array2 [3:9][8:4];
  function new();
    unpacked_array = '{ '{default: '{default: 'h0}},
                        '{default: '{default: 'h1}},
                        '{default: '{default: 'h2}}};
    unpacked_array1 = '{default: '{default: 0}};
    unpacked_array2 = '{default: '{default: 0}};
  endfunction

  function void check_randomization();
    // non-standard foreach loop
    foreach (unpacked_array[i]) begin
      foreach (unpacked_array[i][j]) begin
        `check_rand(this, this.unpacked_array[i][j])
      end
    end
    foreach (unpacked_array1[i, j]) begin
      `check_rand(this, this.unpacked_array1[i][j])
    end
    foreach (unpacked_array2[i, j]) begin
      `check_rand(this, this.unpacked_array2[i][j])
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
    end
  endfunction

  function void check_randomization();
    foreach (dynamic_array_1d[i]) begin
      `check_rand(this, dynamic_array_1d[i])
    end

    foreach (dynamic_array_2d[i, j]) begin
      `check_rand(this, dynamic_array_2d[i][j])
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

class unconstrained_struct_array_test;

  typedef struct {
    rand int field_a;
    rand int field_b;
  } simple_struct_t;
  rand simple_struct_t struct_array_1[3]; // Unpacked array
  rand simple_struct_t struct_array_2[][];  // Dynamic array

  function new();
    struct_array_1 = '{'{default: 0}, '{default: 1}, '{default: 2}};

    struct_array_2 = new[3];
    foreach (struct_array_2[i]) begin
      struct_array_2[i] = new[4];
    end
  endfunction

  function void check_randomization();
    foreach (struct_array_1[i]) begin
      `check_rand(this, struct_array_1[i].field_a)
      `check_rand(this, struct_array_1[i].field_b)
    end
    foreach (struct_array_2[i, j]) begin
      `check_rand(this, struct_array_2[i][j].field_a)
      `check_rand(this, struct_array_2[i][j].field_b)
    end
  endfunction

endclass

class unconstrained_associative_array_test;

  rand int associative_array_1d[string];
  rand int associative_array_3d[string][string][string];
  string key1, key2, key3;

  function new();
    associative_array_1d["key1"] = 1;
    associative_array_1d["key2"] = 2;

    associative_array_3d["key1"]["subkey1"]["subsubkey1"] = 1;
    associative_array_3d["key1"]["subkey1"]["subsubkey2"] = 2;
    associative_array_3d["key1"]["subkey2"]["subsubkey1"] = 3;
    associative_array_3d["key1"]["subkey3"]["subsubkey1"] = 4;
    associative_array_3d["key1"]["subkey3"]["subsubkey2"] = 5;
    associative_array_3d["key1"]["subkey3"]["subsubkey3"] = 6;
    associative_array_3d["key2"]["subkey1"]["subsubkey1"] = 7;
    associative_array_3d["key2"]["subkey1"]["subsubkey2"] = 8;
    associative_array_3d["key2"]["subkey2"]["subsubkey1"] = 9;
    associative_array_3d["key2"]["subkey3"]["subsubkey1"] = 10;
    associative_array_3d["key2"]["subkey3"]["subsubkey2"] = 11;
  endfunction

  function void check_randomization();
    `check_rand(this, associative_array_1d["key1"]);
    `check_rand(this, associative_array_1d["key2"]);

    foreach(associative_array_3d[key1, key2, key3]) begin
      `check_rand(this, associative_array_3d[key1][key2][key3]);
    end
  endfunction

endclass

class unconstrained_queue_test;

  rand int queue_array_1d[$];
  rand int queue_array_2d[$][$];

  function new();
    queue_array_1d = {};
    for (int i = 0; i < 8; i++) begin
        queue_array_1d.push_back('h0 + i);
    end
    queue_array_2d = {};
    queue_array_2d[0] = '{1, 2, 3};
    queue_array_2d[1] = '{4, 5, 6, 0, 10};
    queue_array_2d[2] = '{6, 7, 8, 9};
  endfunction

  function void check_randomization();
    foreach (queue_array_1d[i]) begin
      `check_rand(this, queue_array_1d[i]);
    end
    foreach(queue_array_2d[i, j]) begin
      `check_rand(this, queue_array_2d[i][j]);
    end
  endfunction

endclass

module t_rand_mixed_array_types;
  unconstrained_packed_array_test  packed_class;
  unconstrained_unpacked_array_test unpacked_class;
  unconstrained_dynamic_array_test dynamic_class;
  unconstrained_struct_with_array_test struct_with_array_class;
  unconstrained_struct_array_test struct_array_class;
  unconstrained_associative_array_test associative_array_class;
  unconstrained_queue_test queue_class;

  initial begin
    // Test 1: Packed Array Unconstrained Test
    packed_class = new();
    repeat(2) begin
      packed_class.check_randomization();
      // Display the randomized packed array
      $display("Randomized Packed Array:");
      foreach (packed_class.packed_array[i, j, k]) begin
        $display("packed_array[%0d][%0d][%0d] = %0h", i, j, k, packed_class.packed_array[i][j][k]);
      end
    end

    // Test 2: Unpacked Array Unconstrained Test
    unpacked_class = new();
    repeat(2) begin
      unpacked_class.check_randomization();
      // Display the randomized unpacked array
      $display("Randomized Unpacked Array:");
      foreach (unpacked_class.unpacked_array[i, j]) begin
        $display("unpacked_array[%0d][%0d] = %0h", i, j, unpacked_class.unpacked_array[i][j]);
      end
    end

    // Test 3: Dynamic Array Unconstrained Test
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

    // Test 5: Associative Array Unconstrained Test
    associative_array_class = new();
    repeat(2) begin
      associative_array_class.check_randomization();
      // Display the randomized associative array 1D
      $display("Randomized Associative Array 1D:");
      $display("associative_array_1d[\"key1\"] = %0d", associative_array_class.associative_array_1d["key1"]);
      $display("associative_array_1d[\"key2\"] = %0d", associative_array_class.associative_array_1d["key2"]);

      // Display the randomized associative array 3D
      $display("Randomized Associative Array 3D:");
      foreach(associative_array_class.associative_array_3d[key1, key2, key3]) begin
        $display("associative_array_3d[\"%s\"][\"%s\"][\"%s\"] = %0d", key1, key2, key3, associative_array_class.associative_array_3d[key1][key2][key3]);
      end
    end

    // Test 6: Queue Unconstrained Test
    queue_class = new();
    repeat(2) begin
      queue_class.check_randomization();
      // Display the randomized queue array 1D
      $display("Randomized Queue Array 1D:");
      foreach (queue_class.queue_array_1d[i]) begin
        $display("queue_array_1d[%0d] = %0d", i, queue_class.queue_array_1d[i]);
      end

      // Display the randomized queue array 2D
      $display("Randomized Queue Array 2D:");
      foreach (queue_class.queue_array_2d[i, j]) begin
        $display("queue_array_2d[%0d][%0d] = %0d", i, j, queue_class.queue_array_2d[i][j]);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
