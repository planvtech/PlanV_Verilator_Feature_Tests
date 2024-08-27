class unconstrained_packed_array;

  rand bit [3:0] packed_array [4];

endclass

module packed_array_unconstrained_test;

  unconstrained_packed_array my_array;

  initial begin
    my_array = new();
    if (!my_array.randomize()) begin
      $display("Packed array randomization failed.");
      $stop;
    end

    $display("Packed array values:");
    for (int i = 0; i < 4; i++) begin
      $display("packed_array[%0d] = %0h", i, my_array.packed_array[i]);
    end

    $finish;
  end

endmodule
