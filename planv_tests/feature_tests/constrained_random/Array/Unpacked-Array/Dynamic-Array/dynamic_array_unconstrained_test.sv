module dynamic_array_unconstrained_test;

  // Dynamic array declaration
  rand int dynamic_array [];

  initial begin
    // Initialize the dynamic array with a size of 5
    dynamic_array = new[5];

    // Randomization of the dynamic array without constraints
    if (!dynamic_array.randomize()) begin
      $display("Dynamic array randomization failed.");
    end else begin
      $display("Dynamic array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Dynamic array values:");
    for (int i = 0; i < dynamic_array.size(); i++) begin
      $display("dynamic_array[%0d] = %0d", i, dynamic_array[i]);
    end
  end

endmodule
