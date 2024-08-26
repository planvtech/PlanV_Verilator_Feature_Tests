module packed_array_unconstrained_test;

  // Packed array declaration
  rand bit [3:0] packed_array [4];

  initial begin
    // Randomization of the packed array without constraints
    if (!packed_array.randomize()) begin
      $display("Packed array randomization failed.");
    end else begin
      $display("Packed array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Packed array values:");
    for (int i = 0; i < 4; i++) begin
      $display("packed_array[%0d] = %0h", i, packed_array[i]);
    end
  end

endmodule
