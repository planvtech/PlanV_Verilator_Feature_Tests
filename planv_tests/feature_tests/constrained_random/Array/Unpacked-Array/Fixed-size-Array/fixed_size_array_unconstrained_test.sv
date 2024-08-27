class unconstrained_fixed_size_array;

  rand bit [7:0] fixed_size_array [4];

endclass

module fixed_size_array_unconstrained_test;

  unconstrained_fixed_size_array my_array;

  initial begin
    my_array = new();

    // Randomization of the fixed-size array without constraints
    if (!my_array.randomize()) begin
      $display("Fixed-size array randomization failed.");
      $stop;
    end

    // Displaying the values after randomization
    $display("Fixed-size array values:");
    for (int i = 0; i < 4; i++) begin
      $display("fixed_size_array[%0d] = %0h", i, my_array.fixed_size_array[i]);
    end

    $finish;
  end

endmodule
