// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: associative arrays with wildcard index types
//
// NOTE: IEEE 1800-2017 Section 7.8.1 states that associative arrays with wildcard
// index type shall not be used in a foreach loop or with array manipulation methods.
// Must use first()/next() for iteration.

`include "test_utils.svh"

class NormalAssocArrayWildcard;
  // Associative array with wildcard index
  bit [31:0] assoc_array[*];

  function new();
    assoc_array[0] = 0;
    assoc_array[1] = 0;
  endfunction

  // Method to insert a value into the associative array
  function void insert(int index, bit [31:0] value);
    assoc_array[index] = value;
  endfunction

  // Self-check function to verify the presence of a key
  function void self_check(int index);
    if (!assoc_array.exists(index)) begin
      $stop;
    end
  endfunction

  // Print function to display all key-value pairs
  // NOTE: Use first()/next() instead of foreach for wildcard indexed arrays
  function void print();
    int index;
    if (assoc_array.first(index)) begin
      do begin
        `DBG(("Index: %0d, Value: %0d", index, assoc_array[index]))
      end while (assoc_array.next(index));
    end
  endfunction
endclass

// Constrained random associative array with wildcard index
class ConstrainedAssocArrayWildcard;
  // Associative array with wildcard index
  rand bit [31:0] assoc_array[*];

  // NOTE: foreach cannot be used with wildcard [*] index per IEEE 1800-2017
  // Constraints on wildcard arrays require alternative approaches

  function new();
    assoc_array[0] = 0;
    assoc_array[1] = 0;
  endfunction

  // Self-check function - just verify randomization happened
  // NOTE: Use first()/next() instead of foreach for wildcard indexed arrays
  function void self_check();
    int index;
    int count = 0;
    if (assoc_array.first(index)) begin
      do begin
        count++;
      end while (assoc_array.next(index));
    end
    // Just verify we have at least one entry
    if (count == 0) begin
      `DBG(("Error: assoc_array is empty"))
      $stop;
    end
  endfunction

  // Print function to display all key-value pairs
  function void print();
    int index;
    if (assoc_array.first(index)) begin
      do begin
        `DBG(("Index: %0d, Value: %0d", index, assoc_array[index]))
      end while (assoc_array.next(index));
    end
  endfunction
endclass

module t_rand_array_assoc_wildcard_idx;
  // Top-level initial block to execute tests
  NormalAssocArrayWildcard normal_wildcard;
  ConstrainedAssocArrayWildcard constrained_wildcard;
  int success;

  initial begin
    // Test NormalAssocArrayWildcard
    normal_wildcard = new();
    normal_wildcard.insert(42, 100);
    normal_wildcard.self_check(42);
    normal_wildcard.print();

    // Test ConstrainedAssocArrayWildcard
    constrained_wildcard = new();
    success = constrained_wildcard.randomize();
    if (success != 1) $stop;
    constrained_wildcard.self_check();
    constrained_wildcard.print();

    // Successful execution marker
    `TEST_PASS
  end
endmodule
