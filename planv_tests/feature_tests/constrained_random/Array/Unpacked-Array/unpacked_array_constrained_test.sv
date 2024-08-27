class constrained_unpacked_array;

  rand bit [7:0] unpacked_array [4];

  // Constraints
  constraint unpacked_array_constraints {
    unpacked_array[0] == 8'hAA;
    unpacked_array[1] inside {8'h10, 8'h20, 8'h30};
    unpacked_array[2] > 8'h05;
    unpacked_array[3] < 8'hF0;
  }

endclass

module unpacked_array_constrained_test;

  constrained_unpacked_array my_array;

  initial begin
    my_array = new();

    // Randomization of the unpacked array with constraints
    if (!my_array.randomize()) begin
      $display("Constrained unpacked array randomization failed.");
      $stop;
    end

    // Displaying the values after randomization
    $display("Unpacked array values:");
    for (int i = 0; i < 4; i++) begin
      $display("unpacked_array[%0d] = %0h", i, my_array.unpacked_array[i]);
    end

    $finish;
  end

endmodule
