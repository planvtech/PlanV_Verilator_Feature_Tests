class my_rand_test;

  rand bit [7:0] data[5]; 

  constraint c_data {
    foreach (data[i]) {
      data[i] inside {8'h10, 8'h20, 8'h30, 8'h40, 8'h50};
    }
  }

  task run;
    if (!randomize()) begin
      $display("Randomization failed!");
    end else begin
      $display("Randomized unpacked array:");
      foreach (data[i]) begin
        $display("data[%0d] = %h", i, data[i]);
      end
    end
  endtask

endclass


class my_2d_rand_test;

  rand bit [7:0] data[3][3];

  constraint c_data {
    foreach (data[i, j]) {
      data[i][j] >= 8'h10;
      data[i][j] <= 8'h50;
    }
  }

  task run;
    if (!randomize()) begin
      $display("Randomization failed!");
    end else begin

      $display("Randomized 2D unpacked array:");
      foreach (data[i, j]) begin
        $display("data[%0d][%0d] = %h", i, j, data[i][j]);
      end
    end
  endtask

endclass

class my_3d_rand_test;

  rand bit [7:0] data[2][2][2];

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

  task run;
    if (!randomize()) begin
      $display("Randomization failed!");
    end else begin
      $display("Randomized 3D unpacked array:");
      foreach (data[i, j, k]) begin
        $display("data[%0d][%0d][%0d] = %h", i, j, k, data[i][j][k]);
      end
    end
  endtask

endclass

module unpacked_array_constrained_test_1;

  my_rand_test rand_test_1;
  my_2d_rand_test rand_test_2;
  my_3d_rand_test rand_test_3;

  initial begin
    rand_test_1 = new();
    rand_test_1.run();

    rand_test_2 = new();
    rand_test_2.run();

    rand_test_3 = new();
    rand_test_3.run();
    $finish;
  end

endmodule
