// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class constrained_integral_associative_array;

  rand int associative_array_1 [int];
  rand int associative_array_2 [int][int];

  // Constraints
  constraint associative_array_constraints {
    associative_array_1[0] == 100;
    associative_array_1[1] inside {200, 300, 400};
    foreach (associative_array_2[i, j]) {
      associative_array_2[i][j] < 50;
    }
  }

  // Self-check function to validate the constraints
  function void check();
    if (associative_array_1[0] != 100) begin
      $display("Error: associative_array_1[0] = %0d, expected 100", associative_array_1[0]);
      $stop;
    end
    if (associative_array_1[1] != 200 &&
        associative_array_1[1] != 300 &&
        associative_array_1[1] != 400) begin
      $display("Error: associative_array_1[1] = %0d, expected one of {200, 300, 400}", associative_array_1[1]);
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
    
    // Initialize the associative arrays with some values
    my_array.associative_array_1[0] = 4;
    my_array.associative_array_1[1] = 5;

    my_array.associative_array_2[0][0] = 22;
    my_array.associative_array_2[1][1] = 34;

    // Randomization of the associative arrays with constraints
    if (!my_array.randomize()) begin
      $display("Constrained integral associative array randomization failed.");
      $stop;
    end

    // Self-check to validate the randomization
    my_array.check();

    // Displaying the values after randomization
    $display("Associative array values after randomization:");
    foreach (my_array.associative_array_1[i]) begin
      $display("associative_array_1[%0d] = %0d", i, my_array.associative_array_1[i]);
    end

    foreach (my_array.associative_array_2[i, j]) begin
      $display("associative_array_2[%0d][%0d] = %0d", i, j, my_array.associative_array_2[i][j]);
    end

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
