module associative_array_constrained_test;

  // Associative array declaration
  rand int associative_array [string];

  // Constraints
  constraint associative_array_constraints {
    associative_array["key1"] == 100;
    associative_array["key2"] inside {200, 300, 400};
  }

  initial begin
    // Initialize the associative array with some keys
    associative_array["key1"] = 0;
    associative_array["key2"] = 0;

    // Randomization of the associative array with constraints
    if (!this.randomize() with {associative_array_constraints}) begin
      $display("Constrained associative array randomization failed.");
    end else begin
      $display("Constrained associative array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Associative array values:");
    $display("associative_array[\"key1\"] = %0d", associative_array["key1"]);
    $display("associative_array[\"key2\"] = %0d", associative_array["key2"]);
  end

endmodule
