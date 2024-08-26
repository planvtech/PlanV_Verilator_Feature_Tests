module fixed_size_array_constrained_test;

  // Fixed-size array declaration
  rand bit [7:0] fixed_size_array [4];

  // Constraints
  constraint fixed_size_array_constraints {
    fixed_size_array[0] == 8'h01;
    fixed_size_array[1] inside {8'hA0, 8'hB0, 8'hC0};
    fixed_size_array[2] > 8'h10;
    fixed_size_array[3] < 8'hFF;
  }

  initial begin
    // Randomization of the fixed-size array with constraints
    if (!this.randomize() with {fixed_size_array_constraints}) begin
      $display("Constrained fixed-size array randomization failed.");
    end else begin
      $display("Constrained fixed-size array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Fixed-size array values:");
    for (int i = 0; i < 4; i++) begin
      $display("fixed_size_array[%0d] = %0h", i, fixed_size_array[i]);
    end
  end

endmodule
