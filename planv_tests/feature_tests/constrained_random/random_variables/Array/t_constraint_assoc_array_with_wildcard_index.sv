// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

// Normal associative array with wildcard index
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
  function void print();
    int index;
    if (assoc_array.first(index)) begin
      do begin
        $display("Index: %0d, Value: %0d", index, assoc_array[index]);
      end while (assoc_array.next(index));
    end
  endfunction
endclass

// Constrained random associative array with wildcard index
class ConstrainedAssocArrayWildcard;
  // Associative array with wildcard index
  rand bit [31:0] assoc_array[*];

  // Constraint to limit values
  constraint value_limit {
    foreach (assoc_array[i]) {
      assoc_array[i] < 100; // Values must be less than 100
    }
  }

  function new();
    assoc_array[0] = 0;
    assoc_array[1] = 0;
  endfunction

  // Self-check function to verify constraints
  function void self_check();
    foreach (assoc_array[i]) begin
      if (assoc_array[i] >= 100) begin
        $stop;
      end
    end
  endfunction

  // Print function to display all key-value pairs
  function void print();
    int index;
    if (assoc_array.first(index)) begin
      do begin
        $display("Index: %0d, Value: %0d", index, assoc_array[index]);
      end while (assoc_array.next(index));
    end
  endfunction
endclass

module t_constraint_assoc_array_with_wildcard_index;
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
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
