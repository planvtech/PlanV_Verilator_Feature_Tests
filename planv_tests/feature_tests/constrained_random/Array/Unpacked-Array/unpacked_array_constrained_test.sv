module unpacked_array_constrained_test;

  // Unpacked array declaration
  rand bit [7:0] unpacked_array [4];

  // Constraints
  constraint unpacked_array_constraints {
    unpacked_array[0] == 8'hAA;
    unpacked_array[1] inside {8'h10, 8'h20, 8'h30};
    unpacked_array[2] > 8'h05;
    unpacked_array[3] < 8'hF0;
  }

  initial begin
    // Randomization of the unpacked array with constraints
    if (!this.randomize() with {unpacked_array_constraints}) begin
      $display("Constrained unpacked array randomization failed.");
    end else begin
      $display("Constrained unpacked array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Unpacked array values:");
    for (int i = 0; i < 4; i++) begin
      $display("unpacked_array[%0d] = %0h", i, unpacked_array[i]);
    end
  end

endmodule
