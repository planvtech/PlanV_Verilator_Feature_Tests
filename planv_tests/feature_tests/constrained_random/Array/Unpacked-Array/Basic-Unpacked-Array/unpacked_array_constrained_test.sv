class constrained_unpacked_array;

  rand bit unpacked_array1 [2][3]; // using size, same with using range [0:1][0:2], 2 rows 3 cols bit
  rand bit [2:0] [15:0] unpacked_array2 [4][8];  // 2 rows 3 cols 3 16-bits
  // Constraints
  constraint unpacked_array1_constraints {
    unpacked_array1[0][0] == 1'b1;
    unpacked_array1[0][1] == 1;
    unpacked_array1[0][2] == 1;
    unpacked_array1[1][0] == 0;
    unpacked_array1[1][1] == 0;
    unpacked_array1[1][2] == 0;
  }
  constraint unpacked_array2_constraints {
    unpacked_array2[0][0][0][15:8] == 8'hCA;
    unpacked_array2[0][0][0][7:0] inside {8'hCA, 8'hFE};
    unpacked_array2[0][0][1] == 16'hAAAA;

    unpacked_array2[0][1][0] == 16'hFACE;
    unpacked_array2[0][1][1] == 16'hBBBB;

    unpacked_array2[0][2][0] inside {16'hCAFE, 16'hFACE};
    unpacked_array2[0][2][1] == 16'hCCCC;
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
    $display("Unpacked array1 values:");
    foreach (my_array.unpacked_array1[i]) 
      foreach (my_array.unpacked_array1[i][j]) begin
        $display("unpacked_array1[%0d][%0d] = %0b", i, j, my_array.unpacked_array1[i][j]);
      end

    $display("Unpacked array2 values:");
    foreach (my_array.unpacked_array2[i]) 
      foreach (my_array.unpacked_array2[i][j]) begin
        for (int n = 0; n < 3; n++) begin
          $display("unpacked_array2[%0d][%0d][%0d] = %0h", i, j, n, my_array.unpacked_array2[i][j][n]);
        end
      end

    $finish;
  end

endmodule
