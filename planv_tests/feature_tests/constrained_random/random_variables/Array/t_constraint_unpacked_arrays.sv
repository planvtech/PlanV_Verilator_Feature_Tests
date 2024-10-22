// DESCRIPTION: PlanV Verilator Constrained Randomization Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class ConstrainedRandArrayTest1D;
  rand bit [7:0] data[5];

  // Constraints
  constraint c_data {
    foreach (data[i]) {
      data[i] inside {8'h10, 8'h20, 8'h30, 8'h40, 8'h50};
    }
  }

  // Self-check using if-else for validation
  function void check();
    foreach (data[i]) begin
      if (data[i] inside {8'h10, 8'h20, 8'h30, 8'h40, 8'h50}) begin
        $display("data[%0d] = %h is valid", i, data[i]);
      end else begin
        $display("Error: data[%0d] = %h is out of bounds", i, data[i]);
        $stop;
      end
    end
  endfunction
endclass


class ConstrainedRandArrayTest2D;
  rand bit [7:0] data[3][3];

  // Constraints
  constraint c_data {
    foreach (data[i, j]) {
      data[i][j] >= 8'h10;
      data[i][j] <= 8'h50;
    }
  }

  // Self-check using if-else for validation
  function void check();
    foreach (data[i, j]) begin
      if (data[i][j] >= 8'h10 && data[i][j] <= 8'h50) begin
        $display("data[%0d][%0d] = %h is valid", i, j, data[i][j]);
      end else begin
        $display("Error: data[%0d][%0d] = %h is out of bounds", i, j, data[i][j]);
        $stop;
      end
    end
  endfunction
endclass


class ConstrainedRandArrayTest3D;
  rand bit [7:0] data[2][2][2];

  // Constraints
  constraint c_data {
    foreach (data[i, j, k]) {
      data[i][j][k] >= 8'h10;
      data[i][j][k] <= 8'h50;
      if (i > 0) {
        data[i][j][k] > data[i-1][j][k] + 8'h05;
      }
      if (j > 0) {
        data[i][j][k] > data[i][j-1][k];
      }
    }
  }

  // Self-check using if-else for validation
  function void check();
    foreach (data[i, j, k]) begin
      if (data[i][j][k] >= 8'h10 && data[i][j][k] <= 8'h50) begin
        if (i > 0 && data[i][j][k] <= data[i-1][j][k] + 8'h05) begin
          $display("Error: data[%0d][%0d][%0d] = %h violates i > 0 constraint", i, j, k, data[i][j][k]);
          $stop;
        end
        if (j > 0 && data[i][j][k] <= data[i][j-1][k]) begin
          $display("Error: data[%0d][%0d][%0d] = %h violates j > 0 constraint", i, j, k, data[i][j][k]);
          $stop;
        end
        $display("data[%0d][%0d][%0d] = %h is valid", i, j, k, data[i][j][k]);
      end else begin
        $display("Error: data[%0d][%0d][%0d] = %h is out of bounds", i, j, k, data[i][j][k]);
        $stop;
      end
    end
  endfunction
endclass


module t_constraint_unpacked_arrays;
  ConstrainedRandArrayTest1D rand_test_1;
  ConstrainedRandArrayTest2D rand_test_2;
  ConstrainedRandArrayTest3D rand_test_3;

  initial begin
    // Test 1: Randomization for 1D array
    $display("Test 1: Randomization for 1D array:");
    rand_test_1 = new();
    repeat(2) begin
      if (!rand_test_1.randomize()) begin
        $display("Randomization failed for 1D array.");
        $stop;
      end
      rand_test_1.check();
    end

    // Test 2: Randomization for 2D array
    $display("Test 2: Randomization for 2D array:");
    rand_test_2 = new();
    repeat(2) begin
      if (!rand_test_2.randomize()) begin
        $display("Randomization failed for 2D array.");
        $stop;
      end
      rand_test_2.check();
    end

    // Test 3: Randomization for 3D array
    $display("Test 3: Randomization for 3D array:");
    rand_test_3 = new();
    repeat(2) begin
      if (!rand_test_3.randomize()) begin
        $display("Randomization failed for 3D array.");
        $stop;
      end
      rand_test_3.check();
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
