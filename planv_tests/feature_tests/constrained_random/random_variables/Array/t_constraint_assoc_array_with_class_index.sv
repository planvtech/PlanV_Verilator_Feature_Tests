// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

// Class used as a key in associative arrays
class KeyClass;
  rand bit [31:0] id;

  constraint valid_id {
    id < 1000;
  }

  function bit equals(ref KeyClass rhs);
    return id == rhs.id;
  endfunction

  function void print();
    $display("KeyClass id: %0d", id);
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
        $display("Key ID: %0d, Value: %0d", key.id, assoc_array[key]);
      end while (assoc_array.next(key));
    end
  endfunction
endclass

// Constrained random associative array with class keys
class ConstrainedAssocArrayClass;
  // Associative array with class keys
  rand bit [31:0] assoc_array[KeyClass];

  // Constraint to limit values
  constraint value_limit {
    foreach (assoc_array[key]) {
      assoc_array[key] < 32'd100; // Values must be less than 100
    }
  }

  function new();
    KeyClass key = new();
    key.id = 7;
    assoc_array[key] = 32'h00000000;
  endfunction

  // Self-check function to verify constraints
  function void self_check();
    foreach (assoc_array[key]) begin
      if (assoc_array[key] >= 32'd100) begin
        $stop;
      end
    end
  endfunction

  // Print function to display all key-value pairs
  function void print();
    KeyClass key;
    if (assoc_array.first(key)) begin
      do begin
        $display("Key ID: %0d, Value: %0d", key.id, assoc_array[key]);
      end while (assoc_array.next(key));
    end
  endfunction
endclass

module t_constraint_assoc_array_with_class_index;
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
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
