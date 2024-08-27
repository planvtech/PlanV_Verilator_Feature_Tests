class constrained_packed_array;

  rand bit [2:0] [15:0] packed_array; // 3 16-bits

  constraint packed_array_constraints {
    packed_array[0][15:8] == 8'hCA;
    packed_array[0][7:0] inside {8'hCA, 8'hFE};
    packed_array[1][15:8] == 8'hFA;
    packed_array[1][7:0] == 8'hCE;
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
    for (int i = 0; i < 3; i++) begin
      $display("packed_array[%0d] = %0h", i, my_array.packed_array[i]);
    end

    $finish;
  end

endmodule
