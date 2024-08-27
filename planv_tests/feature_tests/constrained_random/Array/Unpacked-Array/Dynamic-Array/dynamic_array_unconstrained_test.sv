class unconstrained_dynamic_array;

  rand int dynamic_array [];

endclass

module dynamic_array_unconstrained_test;

  unconstrained_dynamic_array my_array;

  initial begin
    my_array = new();

    // Initialize the dynamic array with a size of 5
    my_array.dynamic_array = new[5];

    // Randomization of the dynamic array without constraints
    if (!my_array.randomize()) begin
      $display("Dynamic array randomization failed.");
      $stop;
    end

    // Displaying the values after randomization
    $display("Dynamic array values:");
    for (int i = 0; i < my_array.dynamic_array.size(); i++) begin
      $display("dynamic_array[%0d] = %0d", i, my_array.dynamic_array[i]);
    end

    $finish;
  end

endmodule
