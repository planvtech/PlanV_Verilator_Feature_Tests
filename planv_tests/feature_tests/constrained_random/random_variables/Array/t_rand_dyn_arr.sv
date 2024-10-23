// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) begin \
      $display("Error: Randomization failed for %s", field); \
      $stop; \
   end \
end

class dynamic_arrays;

    rand int dyn_arr[][];
    rand int dynamic_array_1d[]; // 1D dynamic array
    rand int dynamic_array_2d[][]; // 2D dynamic array
    rand int dynamic_array_3d[][][]; // 3D dynamic array

    function new();
        // Initialize 2D array dyn_arr
        dyn_arr = '{'{1, 2, 3}, '{4, 5, 6, 0, 10}, '{6, 7, 8, 9}};
        foreach(dyn_arr[i]) begin
            foreach(dyn_arr[i][j]) begin
                $display("i = %d, j = %d." , i, j);
            end
        end
        $display("--------------------------------------------");
        foreach(dyn_arr[i, j]) begin
            $display("i = %d, j = %d." , i, j);
        end

        // Initialize 1D dynamic array with size 5
        dynamic_array_1d = new[5];

        // Initialize 2D dynamic array with size 5x4
        dynamic_array_2d = new[5];
        for (int i = 0; i < 5; i++) begin
          dynamic_array_2d[i] = new[4];
        end

        // Initialize 3D dynamic array with size 5x4x3
        dynamic_array_3d = new[5];
        for (int i = 0; i < 5; i++) begin
          dynamic_array_3d[i] = new[4];
          for (int j = 0; j < 4; j++) begin
            dynamic_array_3d[i][j] = new[3];
          end
        end
    endfunction

    // Self-check function to validate randomization using check_rand
    function void check();
      foreach (dyn_arr[i, j]) begin
        `check_rand(this, dyn_arr[i][j]);
      end

      foreach (dynamic_array_1d[i]) begin
        `check_rand(this, dynamic_array_1d[i]);
      end

      foreach (dynamic_array_2d[i, j]) begin
        `check_rand(this, dynamic_array_2d[i][j]);
      end

      foreach (dynamic_array_3d[i, j, k]) begin
        `check_rand(this, dynamic_array_3d[i][j][k]);
      end
    endfunction

endclass

module t_rand_dyn_arr;

  dynamic_arrays cl;

  initial begin
    cl = new();

    // Display initial content of dyn_arr
    $display("Initial Dyn_arr Content:");
    $display("%p", cl.dyn_arr);

    // Randomization of dynamic arrays
    if (!cl.randomize()) begin
      $display("Dynamic arrays randomization failed.");
      $stop;
    end

    // Self-check to validate the randomization using check_rand
    cl.check();

    // Display randomization result
    $display("Dyn_arr Content after randomization:");
    $display("%p", cl.dyn_arr);

    // Display 1D dynamic array values
    $display("1D Dynamic array values:");
    for (int i = 0; i < cl.dynamic_array_1d.size(); i++) begin
      $display("dynamic_array_1d[%0d] = %0d", i, cl.dynamic_array_1d[i]);
    end

    // Display 2D dynamic array values
    $display("2D Dynamic array values:");
    for (int i = 0; i < cl.dynamic_array_2d.size(); i++) begin
      for (int j = 0; j < cl.dynamic_array_2d[i].size(); j++) begin
        $display("dynamic_array_2d[%0d][%0d] = %0d", i, j, cl.dynamic_array_2d[i][j]);
      end
    end

    // Display 3D dynamic array values
    $display("3D Dynamic array values:");
    for (int i = 0; i < cl.dynamic_array_3d.size(); i++) begin
      for (int j = 0; j < cl.dynamic_array_3d[i].size(); j++) begin
        for (int k = 0; k < cl.dynamic_array_3d[i][j].size(); k++) begin
          $display("dynamic_array_3d[%0d][%0d][%0d] = %0d", i, j, k, cl.dynamic_array_3d[i][j][k]);
        end
      end
    end

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
