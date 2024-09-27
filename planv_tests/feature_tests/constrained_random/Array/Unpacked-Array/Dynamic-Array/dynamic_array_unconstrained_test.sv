class unconstrained_dynamic_array;

  // Define a 1D dynamic array
  rand int dynamic_array_1d[];

  // Define a 2D dynamic array
  rand int dynamic_array_2d[][];

  // Define a 3D dynamic array
  rand int dynamic_array_3d[][][];

endclass

module dynamic_array_unconstrained_test;

  unconstrained_dynamic_array my_array;

  initial begin
    my_array = new();

    // Initialize the 1D dynamic array with a size of 5
    my_array.dynamic_array_1d = new[5];

    // Initialize the 2D dynamic array with a size of 5x4
    my_array.dynamic_array_2d = new[5];
    for (int i = 0; i < 5; i++) begin
      my_array.dynamic_array_2d[i] = new[4];
    end

    // Initialize the 3D dynamic array with a size of 5x4x3
    my_array.dynamic_array_3d = new[5];
    for (int i = 0; i < 5; i++) begin
      my_array.dynamic_array_3d[i] = new[4];
      for (int j = 0; j < 4; j++) begin
        my_array.dynamic_array_3d[i][j] = new[3];
      end
    end

    // Randomization of the dynamic arrays
    if (!my_array.randomize()) begin
      $display("Dynamic arrays randomization failed.");
      $stop;
    end

    // Displaying the values after randomization

    // Display 1D dynamic array values
    $display("1D Dynamic array values:");
    for (int i = 0; i < my_array.dynamic_array_1d.size(); i++) begin
      $display("dynamic_array_1d[%0d] = %0d", i, my_array.dynamic_array_1d[i]);
    end

    // Display 2D dynamic array values
    $display("2D Dynamic array values:");
    for (int i = 0; i < my_array.dynamic_array_2d.size(); i++) begin
      for (int j = 0; j < my_array.dynamic_array_2d[i].size(); j++) begin
        $display("dynamic_array_2d[%0d][%0d] = %0d", i, j, my_array.dynamic_array_2d[i][j]);
      end
    end

    // Display 3D dynamic array values
    $display("3D Dynamic array values:");
    for (int i = 0; i < my_array.dynamic_array_3d.size(); i++) begin
      for (int j = 0; j < my_array.dynamic_array_3d[i].size(); j++) begin
        for (int k = 0; k < my_array.dynamic_array_3d[i][j].size(); k++) begin
          $display("dynamic_array_3d[%0d][%0d][%0d] = %0d", i, j, k, my_array.dynamic_array_3d[i][j][k]);
        end
      end
    end

    $finish;
  end

endmodule
