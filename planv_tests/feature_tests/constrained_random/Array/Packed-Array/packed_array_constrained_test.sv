module packed_array_constrained_test;

  // Packed array declaration
  rand bit [3:0] packed_array [4];

  // Constraints
  constraint packed_array_constraints {
    packed_array[0] == 4'hA;
    packed_array[1] inside {4'h3, 4'h7};
    packed_array[2] > 4'h2;
    packed_array[3] < 4'hF;
  }

  initial begin
    // Randomization of the packed array with constraints
    if (!this.randomize() with {packed_array_constraints}) begin
      $display("Constrained packed array randomization failed.");
    end else begin
      $display("Constrained packed array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Packed array values:");
    for (int i = 0; i < 4; i++) begin
      $display("packed_array[%0d] = %0h", i, packed_array[i]);
    end
  end

endmodule
