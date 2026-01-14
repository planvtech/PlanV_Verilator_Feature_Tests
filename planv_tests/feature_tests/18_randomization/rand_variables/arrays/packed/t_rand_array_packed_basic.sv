// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: constraints on packed arrays

`include "test_utils.svh"

class constrained_packed_array;

  rand bit [2:0] [15:0] packed_array; // 3 16-bits

  constraint packed_array_constraints {
    packed_array[0][15:8] == 8'hCA;
    packed_array[0][7:0] inside {8'hCA, 8'hFE};
    packed_array[1][15:8] == 8'hFA;
    packed_array[1][7:0] == 8'hCE;
  }

  // Self-check function to validate the constraints
  function void check();
    if (packed_array[0][15:8] != 8'hCA) begin
      `DBG(("Error: packed_array[0][15:8] = %0h, expected 8'hCA", packed_array[0][15:8]))
      $stop;
    end
    if (packed_array[0][7:0] != 8'hCA && packed_array[0][7:0] != 8'hFE) begin
      `DBG(("Error: packed_array[0][7:0] = %0h, expected 8'hCA or 8'hFE", packed_array[0][7:0]))
      $stop;
    end
    if (packed_array[1][15:8] != 8'hFA) begin
      `DBG(("Error: packed_array[1][15:8] = %0h, expected 8'hFA", packed_array[1][15:8]))
      $stop;
    end
    if (packed_array[1][7:0] != 8'hCE) begin
      `DBG(("Error: packed_array[1][7:0] = %0h, expected 8'hCE", packed_array[1][7:0]))
      $stop;
    end
    `DBG(("Packed array constraint check passed."))
  endfunction

endclass

module t_rand_array_packed_basic;

  constrained_packed_array my_array;

  initial begin
    my_array = new();
    if (!my_array.randomize()) begin
      `DBG(("Constrained packed array randomization failed."))
      $stop;
    end

    // Self-check to validate the randomization
    my_array.check();

    // Additional detailed print information
    `DBG(("Packed array values:"))
    for (int i = 0; i < 3; i++) begin
      `DBG(("packed_array[%0d] = %0h", i, my_array.packed_array[i]))
    end

    // Successful execution marker
    `TEST_PASS
  end

endmodule
