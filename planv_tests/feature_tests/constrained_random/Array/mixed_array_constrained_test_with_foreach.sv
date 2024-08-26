module mixed_array_constrained_test_with_foreach;

  // Unpacked array
  rand bit [7:0] unpacked_array [4];

  // Packed array
  rand bit [3:0] packed_array [4];

  // Dynamic array
  rand int dynamic_array [];

  // Associative array
  rand int associative_array [string];

  // Fixed-size array
  rand bit [7:0] fixed_size_array [4];

  // Queue
  rand int queue_array [$];

  // Constraints
  constraint array_constraints {
    foreach(unpacked_array[i]) unpacked_array[i] inside {8'h00, 8'hFF};
    foreach(packed_array[i]) packed_array[i] inside {4'h1, 4'hE};
    dynamic_array.size() == 5;
    foreach(dynamic_array[i]) dynamic_array[i] inside {[1:10]};
    associative_array["key1"] inside {[100:200]};
    associative_array["key2"] inside {[300:400]};
    foreach(fixed_size_array[i]) fixed_size_array[i] == i;
    foreach(queue_array[i]) queue_array[i] inside {[50:100]};
  }

  initial begin
    // Dynamic array initialization
    dynamic_array = new[5];

    // Associative array initialization
    associative_array["key1"] = 0;
    associative_array["key2"] = 0;

    // Queue initialization
    queue_array.push_back(0);
    queue_array.push_back(0);

    // Unpacked array randomization with constraints
    if (!unpacked_array.randomize() with {array_constraints}) begin
      $display("Constrained unpacked array randomization failed.");
    end

    // Packed array randomization with constraints
    if (!packed_array.randomize() with {array_constraints}) begin
      $display("Constrained packed array randomization failed.");
    end

    // Dynamic array randomization with constraints
    if (!dynamic_array.randomize() with {array_constraints}) begin
      $display("Constrained dynamic array randomization failed.");
    end

    // Associative array randomization with constraints
    if (!associative_array.randomize() with {array_constraints}) begin
      $display("Constrained associative array randomization failed.");
    end

    // Fixed-size array randomization with constraints
    if (!fixed_size_array.randomize() with {array_constraints}) begin
      $display("Constrained fixed-size array randomization failed.");
    end

    // Queue randomization with constraints
    if (!queue_array.randomize() with {array_constraints}) begin
      $display("Constrained queue randomization failed.");
    end

    $display("Constrained Mixed Array Randomization passed.");
  end

endmodule
