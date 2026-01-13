// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

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
      $display("Error: packed_array[0][15:8] = %0h, expected 8'hCA", packed_array[0][15:8]);
      $stop;
    end
    if (packed_array[0][7:0] != 8'hCA && packed_array[0][7:0] != 8'hFE) begin
      $display("Error: packed_array[0][7:0] = %0h, expected 8'hCA or 8'hFE", packed_array[0][7:0]);
      $stop;
    end
    if (packed_array[1][15:8] != 8'hFA) begin
      $display("Error: packed_array[1][15:8] = %0h, expected 8'hFA", packed_array[1][15:8]);
      $stop;
    end
    if (packed_array[1][7:0] != 8'hCE) begin
      $display("Error: packed_array[1][7:0] = %0h, expected 8'hCE", packed_array[1][7:0]);
      $stop;
    end
    $display("Packed array constraint check passed.");
  endfunction

endclass

module t_constraint_packed_array;

  constrained_packed_array my_array;

  initial begin
    my_array = new();
    if (!my_array.randomize()) begin
      $display("Constrained packed array randomization failed.");
      $stop;
    end

    // Self-check to validate the randomization
    my_array.check();

    // Additional detailed print information
    $display("Packed array values:");
    for (int i = 0; i < 3; i++) begin
      $display("packed_array[%0d] = %0h", i, my_array.packed_array[i]);
    end

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
