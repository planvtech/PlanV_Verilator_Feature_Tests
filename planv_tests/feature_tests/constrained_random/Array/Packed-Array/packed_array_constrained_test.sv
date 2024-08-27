class constrained_packed_array;

  rand bit [3:0] packed_array [4];

  constraint packed_array_constraints {
    packed_array[0] == 4'hA;
    packed_array[1] inside {4'h3, 4'h7};
    packed_array[2] > 4'h2;
    packed_array[3] < 4'hF;
  }

endclass

module packed_array_constrained_test;

  constrained_packed_array my_array;

  initial begin
    my_array = new();
    if (!my_array.randomize()) begin
      $display("Constrained packed array randomization failed.");
      $stop;
    end

    $display("Packed array values:");
    for (int i = 0; i < 4; i++) begin
      $display("packed_array[%0d] = %0h", i, my_array.packed_array[i]);
    end

    $finish;
  end

endmodule
