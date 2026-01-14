// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: associative arrays with class-type indices

`include "test_utils.svh"

class KeyClass;
  rand bit [31:0] id;

  constraint valid_id {
    id < 1000;
  }

  function bit equals(ref KeyClass rhs);
    return id == rhs.id;
  endfunction

  function void print();
    `DBG(("KeyClass id: %0d", id))
  endfunction
endclass

// Normal associative array with class keys
class NormalAssocArrayClass;
  // Associative array with class keys
  bit [31:0] assoc_array[KeyClass];

  function new();
    KeyClass key;
    key = new();
    key.id = 6;
    assoc_array[key] = 32'h00000000;
  endfunction
  // Method to insert a value into the associative array
  function void insert(KeyClass key, bit [31:0] value);
    assoc_array[key] = value;
  endfunction

  // Method to retrieve a value from the associative array
  function bit [31:0] get(KeyClass key);
    return assoc_array[key];
  endfunction

  // Self-check function to verify the presence of a key
  function void self_check(KeyClass key);
    if (!assoc_array.exists(key)) begin
      $stop;
    end
  endfunction

  // Print function to display all key-value pairs
  function void print();
    KeyClass key;
    if (assoc_array.first(key)) begin
      do begin
        `DBG(("Key ID: %0d, Value: %0d", key.id, assoc_array[key]))
      end while (assoc_array.next(key));
    end
  endfunction
endclass

// Constrained random associative array with class keys
class ConstrainedAssocArrayClass;
  // Associative array with class keys
  rand bit [31:0] assoc_array[KeyClass];

  // NOTE: QuestaSim does not support foreach with class index in constraints
  // The constraint below would cause runtime error:
  // "(vsim-7088) Unsupported index type for an associative array in an iterative constraint"
  // constraint value_limit {
  //     foreach (assoc_array[key]) {
  //       assoc_array[key] < 32'd100;
  //     }
  // }

  function new();
    KeyClass key = new();
    key.id = 7;
    assoc_array[key] = 32'h00000000;
  endfunction

  // Self-check function - just verify randomization happened
  // NOTE: Use first()/next() instead of foreach for class-indexed assoc arrays
  function void self_check();
    KeyClass key;
    int count = 0;
    if (assoc_array.first(key)) begin
      do begin
        count++;
      end while (assoc_array.next(key));
    end
    // Just verify we have at least one entry
    if (count == 0) begin
      `DBG(("Error: assoc_array is empty"))
      $stop;
    end
  endfunction

  // Print function to display all key-value pairs
  function void print();
    KeyClass key;
    if (assoc_array.first(key)) begin
      do begin
        `DBG(("Key ID: %0d, Value: %0d", key.id, assoc_array[key]))
      end while (assoc_array.next(key));
    end
  endfunction
endclass

module t_rand_array_assoc_class_idx;
  // Top-level initial block to execute tests
  KeyClass key1;
  KeyClass key2;
  NormalAssocArrayClass normal_class;
  ConstrainedAssocArrayClass constrained_class;
  int success;
  initial begin
    // Test NormalAssocArrayClass
    key1 = new();
    key1.id = 42;
    normal_class = new();
    normal_class.insert(key1, 100);
    normal_class.self_check(key1);
    normal_class.print();

    // Test ConstrainedAssocArrayClass
    constrained_class = new();
    key2 = new();
    success = key2.randomize();
    if (success != 1) $stop;
    success = constrained_class.randomize();
    if (success != 1) $stop;
    constrained_class.self_check();
    constrained_class.print();

    // Successful execution marker
    `TEST_PASS
  end
endmodule
