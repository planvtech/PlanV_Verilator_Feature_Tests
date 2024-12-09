// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class constrained_integral_associative_array;

  rand int associative_array_1 [int];
  rand int associative_array_2 [int][int];

  constraint associative_array_constraints {
    associative_array_1[1] == 100;
    associative_array_1[5] inside {200, 300, 400};
    foreach (associative_array_2[i, j]) {
      associative_array_2[i][j] < 50;
    }
  }

  function void check();
    if (associative_array_1[1] != 100) begin
      $display("Error: associative_array_1[1] = %0d, expected 100", associative_array_1[1]);
      $stop;
    end
    if (associative_array_1[5] != 200 &&
        associative_array_1[5] != 300 &&
        associative_array_1[5] != 400) begin
      $display("Error: associative_array_1[5] = %0d, expected one of {200, 300, 400}", associative_array_1[5]);
      $stop;
    end
    foreach (associative_array_2[i, j]) begin
      if (associative_array_2[i][j] >= 50) begin
        $display("Error: associative_array_2[%0d][%0d] = %0d, expected < 50", i, j, associative_array_2[i][j]);
        $stop;
      end
    end
    $display("All constraints validated successfully.");
  endfunction

endclass

module t_constraint_assoc_arr_integral;

  constrained_integral_associative_array my_array;

  initial begin
    my_array = new();

    my_array.associative_array_1[1] = 4;
    my_array.associative_array_1[5] = 5;

    my_array.associative_array_2[0][0] = 22;
    my_array.associative_array_2[0][3] = 34;
    my_array.associative_array_2[6][2] = 212;
    my_array.associative_array_2[6][9] = 314;

    if (!my_array.randomize()) begin
      $display("Constrained integral associative array randomization failed.");
      $stop;
    end

    my_array.check();

    $display("Associative array values after randomization:");
    foreach (my_array.associative_array_1[i]) begin
      $display("associative_array_1[%0d] = %0d", i, my_array.associative_array_1[i]);
    end

    foreach (my_array.associative_array_2[i, j]) begin
      $display("associative_array_2[%0d][%0d] = %0d", i, j, my_array.associative_array_2[i][j]);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
