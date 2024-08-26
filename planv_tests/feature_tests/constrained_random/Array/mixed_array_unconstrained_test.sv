module mixed_array_unconstrained_test;

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

  initial begin
    // Dynamic array initialization
    dynamic_array = new[5];

    // Associative array initialization
    associative_array["key1"] = 0;
    associative_array["key2"] = 0;

    // Queue initialization
    queue_array.push_back(0);
    queue_array.push_back(0);

    // Unpacked array randomization
    if (!unpacked_array.randomize()) begin
      $display("Unpacked array randomization failed.");
    end

    // Packed array randomization
    if (!packed_array.randomize()) begin
      $display("Packed array randomization failed.");
    end

    // Dynamic array randomization
    if (!dynamic_array.randomize()) begin
      $display("Dynamic array randomization failed.");
    end

    // Associative array randomization
    if (!associative_array.randomize()) begin
      $display("Associative array randomization failed.");
    end

    // Fixed-size array randomization
    if (!fixed_size_array.randomize()) begin
      $display("Fixed-size array randomization failed.");
    end

    // Queue randomization
    if (!queue_array.randomize()) begin
      $display("Queue randomization failed.");
    end

    $display("Unconstrained Mixed Array Randomization passed.");
  end

endmodule

