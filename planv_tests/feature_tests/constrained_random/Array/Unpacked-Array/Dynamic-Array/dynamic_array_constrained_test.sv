module dynamic_array_constrained_test;

  // Dynamic array declaration
  rand int dynamic_array [];

  // Constraints
  constraint dynamic_array_constraints {
    dynamic_array.size() == 5; // Fixing the size of the array
    dynamic_array[0] == 10;
    dynamic_array[1] inside {20, 30, 40};
    dynamic_array[2] > 50;
    dynamic_array[3] < 100;
    dynamic_array[4] inside {5, 15, 25};
  }

  initial begin
    // Initialize the dynamic array with a size of 5
    dynamic_array = new[5];

    // Randomization of the dynamic array with constraints
    if (!this.randomize() with {dynamic_array_constraints}) begin
      $display("Constrained dynamic array randomization failed.");
    end else begin
      $display("Constrained dynamic array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Dynamic array values:");
    for (int i = 0; i < dynamic_array.size(); i++) begin
      $display("dynamic_array[%0d] = %0d", i, dynamic_array[i]);
    end
  end

endmodule
