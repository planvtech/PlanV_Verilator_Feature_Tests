// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

// User-defined type for associative array index
typedef struct packed {
  bit [15:0] high;
  bit [15:0] low;
} UserDefinedIndexType;

// Normal associative array with user-defined index
class NormalAssocArrayUserDefined;
  // Associative array with user-defined index
  bit [31:0] assoc_array[UserDefinedIndexType];

  // Method to insert a value into the associative array
  function void insert(UserDefinedIndexType index, bit [31:0] value);
    assoc_array[index] = value;
  endfunction

  // Self-check function to verify the presence of a key
  function void self_check(UserDefinedIndexType index);
    if (!assoc_array.exists(index)) begin
      $stop;
    end
  endfunction

  // Print function to display all key-value pairs
  function void print();
    UserDefinedIndexType index;
    if (assoc_array.first(index)) begin
      do begin
        $display("Index: high=%0d, low=%0d, Value: %0d", index.high, index.low, assoc_array[index]);
      end while (assoc_array.next(index));
    end
  endfunction
endclass

// Constrained random associative array with user-defined index
class ConstrainedAssocArrayUserDefined;
  // Associative array with user-defined index
  rand bit [31:0] assoc_array[UserDefinedIndexType];

  // Constraint to limit values and indices
  constraint valid_entries {
    foreach (assoc_array[i]) {
      assoc_array[i] < 100; // Values must be less than 100
      i.high < 500;         // high field must be less than 500
      i.low > 100;          // low field must be greater than 100
    }
  }

  // Self-check function to verify constraints
  function void self_check();
    foreach (assoc_array[i]) begin
      if (assoc_array[i] >= 100 || i.high >= 500 || i.low <= 100) begin
        $stop;
      end
    end
  endfunction

  // Print function to display all key-value pairs
  function void print();
    UserDefinedIndexType index;
    if (assoc_array.first(index)) begin
      do begin
        $display("Index: high=%0d, low=%0d, Value: %0d", index.high, index.low, assoc_array[index]);
      end while (assoc_array.next(index));
    end
  endfunction
endclass

module t_constraint_assoc_array_with_userDefinedTypes_index;
  // Top-level initial block to execute tests
  initial begin
    // Test NormalAssocArrayUserDefined
    NormalAssocArrayUserDefined normal_user_defined = new();
    UserDefinedIndexType index_normal = '{high: 123, low: 456};
    normal_user_defined.insert(index_normal, 42);
    normal_user_defined.self_check(index_normal);
    normal_user_defined.print();

    // Test ConstrainedAssocArrayUserDefined
    ConstrainedAssocArrayUserDefined constrained_user_defined = new();
    constrained_user_defined.randomize();
    constrained_user_defined.self_check();
    constrained_user_defined.print();

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
