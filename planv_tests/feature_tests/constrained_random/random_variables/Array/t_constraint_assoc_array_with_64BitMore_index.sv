// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

// Class for normal associative array operations
class NormalAssocArray;
  // Associative array with 65-bit index
  bit [31:0] assoc_array[bit[64:0]];

  function new();
    assoc_array[65'd0] = 32'd0;
    assoc_array[65'h1FFFFFFFFFFFFFFFF] = 32'h00000000;
  endfunction
  // Method to insert a value into the associative array
  function void insert(bit [64:0] index, bit [31:0] value);
    assoc_array[index] = value;
  endfunction

  // Method to retrieve a value from the associative array
  function bit [31:0] get(bit [64:0] index);
    return assoc_array[index];
  endfunction

  // Self-check function to verify the presence of a key
  function void self_check(bit [64:0] index);
    if (!assoc_array.exists(index)) begin
      $stop;
    end
  endfunction

  // Print function to display all key-value pairs
  function void print();
    bit [64:0] idx;
    if (assoc_array.first(idx)) begin
      do begin
        $display("Index: %0h, Value: %0h", idx, assoc_array[idx]);
      end while (assoc_array.next(idx));
    end
  endfunction
endclass

// Class for constrained random associative array operations
class ConstrainedAssocArray;
  // Associative array with 65-bit index
  rand bit [31:0] assoc_array[bit[64:0]];

  // Constraint to ensure all indices are odd and values are even
  constraint valid_entries {
      assoc_array[65'd6] == 32'd8;
  }

  function new();
    assoc_array[65'd0] = 32'd0;
    assoc_array[65'd6] = 32'd0;
  endfunction

  // Self-check function to verify constraints
  function void self_check();
    if (assoc_array[65'd6] != 32'd8)
      $stop;
  endfunction

  // Print function to display all key-value pairs
  function void print();
    bit [64:0] idx;
    if (assoc_array.first(idx)) begin
      do begin
        $display("Index: %0d, Value: %0d", idx, assoc_array[idx]);
      end while (assoc_array.next(idx));
    end
  endfunction
endclass

module t_constraint_assoc_array_with_64BitMore_index;

  NormalAssocArray normal;
  ConstrainedAssocArray constrained;
  int success;
  initial begin
    // Instantiate and test NormalAssocArray
    normal = new();
    normal.insert(65'h1FFFFFFFFFFFFFFFF, 32'hDEADBEEF);
    normal.self_check(65'h1FFFFFFFFFFFFFFFF);
    normal.print();

    // Instantiate and test ConstrainedAssocArray
    constrained = new();
    success = constrained.randomize();
    if (success != 1) $stop;
    constrained.self_check();
    constrained.print();

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
