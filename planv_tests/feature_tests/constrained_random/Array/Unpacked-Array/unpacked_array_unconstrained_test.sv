class unconstrained_unpacked_array;

  rand bit [7:0] unpacked_array [4];

endclass

module unpacked_array_unconstrained_test;

  unconstrained_unpacked_array my_array;

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
      $display("unpacked_array[%0d] = %0h", i, my_array.unpacked_array[i]);
    end

    $finish;
  end

endmodule
