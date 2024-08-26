module fixed_size_array_unconstrained_test;

  // Fixed-size array declaration
  rand bit [7:0] fixed_size_array [4];

  initial begin
    // Randomization of the fixed-size array without constraints
    if (!fixed_size_array.randomize()) begin
      $display("Fixed-size array randomization failed.");
    end else begin
      $display("Fixed-size array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Fixed-size array values:");
    for (int i = 0; i < 4; i++) begin
      $display("fixed_size_array[%0d] = %0h", i, fixed_size_array[i]);
    end
  end

endmodule
