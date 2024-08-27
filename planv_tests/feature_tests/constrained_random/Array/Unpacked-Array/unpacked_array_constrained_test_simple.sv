class constrained_unpacked_array;

  rand int unpacked_array [3];
  constraint unpacked_array_constraints {
    unpacked_array[0] == 7;
    unpacked_array[1] == 8;
  }
endclass

module unpacked_array_constrained_test_simple;

  constrained_unpacked_array my_array;

  initial begin
    my_array = new();

    // Randomization of the unpacked array without constraints
    if (!my_array.randomize()) begin
      $display("Unpacked array randomization failed.");
      $stop;
    end

    // Displaying the values after randomization
    $display("Unpacked array values:");
    for (int i = 0; i < 4; i++) begin
      $display("unpacked_array[%0d] = %0b", i, my_array.unpacked_array[i]);
    end

    $finish;
  end

endmodule
