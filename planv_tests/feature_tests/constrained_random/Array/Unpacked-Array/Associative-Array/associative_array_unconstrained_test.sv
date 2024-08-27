class unconstrained_associative_array;

  rand int associative_array [string];

endclass

module associative_array_unconstrained_test;

  unconstrained_associative_array my_array;

  initial begin
    my_array = new();

    // Initialize the associative array with some keys
    my_array.associative_array["key1"] = 0;
    my_array.associative_array["key2"] = 0;

    // Randomization of the associative array without constraints
    if (!my_array.randomize()) begin
      $display("Associative array randomization failed.");
      $stop;
    end

    // Displaying the values after randomization
    $display("Associative array values:");
    $display("associative_array[\"key1\"] = %0d", my_array.associative_array["key1"]);
    $display("associative_array[\"key2\"] = %0d", my_array.associative_array["key2"]);

    $finish;
  end

endmodule
