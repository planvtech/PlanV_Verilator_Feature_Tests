class constrained_dynamic_array;

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

endclass

module dynamic_array_constrained_test;

  constrained_dynamic_array my_array;

  initial begin
    my_array = new();

    // Initialize the dynamic array with a size of 5
    my_array.dynamic_array = new[5];

    // Randomization of the dynamic array with constraints
    if (!my_array.randomize()) begin
      $display("Constrained dynamic array randomization failed.");
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
