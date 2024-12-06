// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class constrained_associative_array;

  rand int associative_array_1 [string];
  rand int associative_array_2 [int];
  rand int unpacked_array [3][2];

  // Constraints
  constraint associative_array_constraints {
    associative_array_1["key1"] == 100;
    associative_array_1["key2"] inside {200, 300, 400};
    associative_array_2[0] < 10;
    associative_array_2[4] < 10;
  }

  constraint unpacked_array_constraints {
    unpacked_array[2][0] == 4;
    unpacked_array[0][1] == 0;
  }

  // Self-check function to validate the constraints
  function void check();
    if (associative_array_1["key1"] != 100) begin
      $display("Error: associative_array_1[\"key1\"] = %0d, expected 100", associative_array_1["key1"]);
      $stop;
    end
    if (associative_array_1["key2"] != 200 &&
        associative_array_1["key2"] != 300 &&
        associative_array_1["key2"] != 400) begin
      $display("Error: associative_array_1[\"key2\"] = %0d, expected one of {200, 300, 400}", associative_array_1["key2"]);
      $stop;
    end
    foreach (associative_array_2[i]) begin
      if (associative_array_2[i] >= 10) begin
        $display("Error: associative_array_2[%0d] = %0d, expected < 10", i, associative_array_2[i]);
        $stop;
      end
    end
    if (unpacked_array[2][0] != 4 || unpacked_array[0][1] != 0) begin
      $display("Error: unpacked_array constraints failed: unpacked_array[2][0] = %0d, unpacked_array[0][1] = %0d",
               unpacked_array[2][0], unpacked_array[0][1]);
      $stop;
    end
    $display("All constraints validated successfully.");
  endfunction

endclass

module t_constraint_assoc_arr;

  constrained_associative_array my_array;

  initial begin
    my_array = new();
    
    // Initialize the associative array with some keys
    my_array.associative_array_1["key1"] = 4;
    my_array.associative_array_1["key2"] = 5;

    my_array.associative_array_2 = '{ 0 : 22, 4 : 34, 16 : 3};

    // Randomization of the associative array with constraints
    if (!my_array.randomize()) begin
      $display("Constrained associative array randomization failed.");
      $stop;
    end

    // Self-check to validate the randomization
    my_array.check();

    // Displaying the values after randomization
    $display("Associative array values after randomization:");
    $display("associative_array_1[\"key1\"] = %0d", my_array.associative_array_1["key1"]);
    $display("associative_array_1[\"key2\"] = %0d", my_array.associative_array_1["key2"]);

    foreach (my_array.associative_array_2[i]) begin
      $display("associative_array_2[%0d] = %0d", i, my_array.associative_array_2[i]);
    end

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
