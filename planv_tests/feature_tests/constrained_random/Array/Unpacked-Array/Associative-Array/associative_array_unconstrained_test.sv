module associative_array_unconstrained_test;

  // Associative array declaration
  rand int associative_array [string];

  initial begin
    // Initialize the associative array with some keys
    associative_array["key1"] = 0;
    associative_array["key2"] = 0;

    // Randomization of the associative array without constraints
    if (!associative_array.randomize()) begin
      $display("Associative array randomization failed.");
    end else begin
      $display("Associative array randomization successful.");
    end

    // Displaying the values after randomization
    $display("Associative array values:");
    $display("associative_array[\"key1\"] = %0d", associative_array["key1"]);
    $display("associative_array[\"key2\"] = %0d", associative_array["key2"]);
  end

endmodule
