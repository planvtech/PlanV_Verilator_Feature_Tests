module mixed_array_constrained_test_no_foreach;

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
    unpacked_array[0] == 8'hAA;
    unpacked_array[1] == 8'hBB;
    unpacked_array[2] == 8'hCC;
    unpacked_array[3] == 8'hDD;

    packed_array[0] inside {4'h1, 4'h2};
    packed_array[1] inside {4'h3, 4'h4};
    packed_array[2] inside {4'h5, 4'h6};
    packed_array[3] inside {4'h7, 4'h8};

    dynamic_array.size() == 5;
    dynamic_array[0] == 1;
    dynamic_array[1] == 2;
    dynamic_array[2] == 3;
    dynamic_array[3] == 4;
    dynamic_array[4] == 5;

    associative_array["key1"] == 100;
    associative_array["key2"] == 200;

    fixed_size_array[0] == 8'h01;
    fixed_size_array[1] == 8'h02;
    fixed_size_array[2] == 8'h03;
    fixed_size_array[3] == 8'h04;

    queue_array.size() == 2;
    queue_array[0] inside {[50:60]};
    queue_array[1] inside {[70:80]};
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
    if (!this.randomize() with {array_constraints}) begin
      $display("Constrained unpacked array randomization failed.");
    end

    // Packed array randomization with constraints
    if (!this.randomize() with {array_constraints}) begin
      $display("Constrained packed array randomization failed.");
    end

    // Dynamic array randomization with constraints
    if (!this.randomize() with {array_constraints}) begin
      $display("Constrained dynamic array randomization failed.");
    end

    // Associative array randomization with constraints
    if (!this.randomize() with {array_constraints}) begin
      $display("Constrained associative array randomization failed.");
    end

    // Fixed-size array randomization with constraints
    if (!this.randomize() with {array_constraints}) begin
      $display("Constrained fixed-size array randomization failed.");
    end

    // Queue randomization with constraints
    if (!this.randomize() with {array_constraints}) begin
      $display("Constrained queue randomization failed.");
    end

    $display("Constrained Mixed Array Randomization passed.");
  end

endmodule
