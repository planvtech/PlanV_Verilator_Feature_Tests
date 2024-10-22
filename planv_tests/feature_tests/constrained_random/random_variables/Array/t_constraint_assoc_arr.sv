// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class constrained_associative_array;

  rand int associative_array [string];

  // Constraints
  constraint associative_array_constraints {
    associative_array["key1"] == 100;
    associative_array["key2"] inside {200, 300, 400};
  }

  // Self-check function to validate the constraints
  function void check();
    if (associative_array["key1"] != 100) begin
      $display("Error: associative_array[\"key1\"] = %0d, expected 100", associative_array["key1"]);
      $stop;
    end
    if (associative_array["key2"] != 200 && associative_array["key2"] != 300 && associative_array["key2"] != 400) begin
      $display("Error: associative_array[\"key2\"] = %0d, expected one of {200, 300, 400}", associative_array["key2"]);
      $stop;
    end
    $display("Associative array constraint check passed.");
  endfunction

endclass

module constraint_rand_associative_array;

  constrained_associative_array my_array;

  initial begin
    my_array = new();
    
    // Initialize the associative array with some keys
    my_array.associative_array["key1"] = 0;
    my_array.associative_array["key2"] = 0;

    // Randomization of the associative array with constraints
    if (!my_array.randomize()) begin
      $display("Constrained associative array randomization failed.");
      $stop;
    end

    // Self-check to validate the randomization
    my_array.check();

    // Displaying the values after randomization
    $display("Associative array values:");
    $display("associative_array[\"key1\"] = %0d", my_array.associative_array["key1"]);
    $display("associative_array[\"key2\"] = %0d", my_array.associative_array["key2"]);

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
