module unpacked_array_unconstrained_test;

  // Unpacked array declaration
  rand bit [7:0] unpacked_array [4];

  initial begin
    // Randomization of the unpacked array without constraints
    if (!unpacked_array.randomize()) begin
      $display("Unpacked array randomization failed.");
    end else begin
      $display("Unpacked array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Unpacked array values:");
    for (int i = 0; i < 4; i++) begin
      $display("unpacked_array[%0d] = %0h", i, unpacked_array[i]);
    end
  end

endmodule
