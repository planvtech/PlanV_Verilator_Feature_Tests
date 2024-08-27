class constrained_associative_array;

  rand int associative_array [string];

  // Constraints
  constraint associative_array_constraints {
    associative_array["key1"] == 100;
    associative_array["key2"] inside {200, 300, 400};
  }

endclass

module associative_array_constrained_test;

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

    // Displaying the values after randomization
    $display("Associative array values:");
    $display("associative_array[\"key1\"] = %0d", my_array.associative_array["key1"]);
    $display("associative_array[\"key2\"] = %0d", my_array.associative_array["key2"]);

    $finish;
  end

endmodule
