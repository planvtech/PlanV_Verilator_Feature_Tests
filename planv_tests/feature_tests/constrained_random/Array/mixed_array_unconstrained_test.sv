class unconstrained_mixed_array;

  rand bit [7:0] unpacked_array [4];
  rand bit [3:0] packed_array [4];
  rand int dynamic_array [];
  rand int associative_array [string];
  rand bit [7:0] fixed_size_array [4];
  rand int queue [$];

endclass

module mixed_array_unconstrained_test;

  unconstrained_mixed_array my_array;

  initial begin
    my_array = new();
    
    // Dynamic array initialization
    my_array.dynamic_array = new[5];

    // Associative array initialization
    my_array.associative_array["key1"] = 0;
    my_array.associative_array["key2"] = 0;

    // Queue initialization
    my_array.queue.push_back(0);
    my_array.queue.push_back(0);

    // Unpacked array randomization
    if (!my_array.randomize()) begin
      $display("Mixed array randomization failed.");
      $stop;
    end

    $display("Unpacked array values:");
    foreach (my_array.unpacked_array[i]) begin
      $display("unpacked_array[%0d] = %0h", i, my_array.unpacked_array[i]);
    end

    $display("Packed array values:");
    foreach (my_array.packed_array[i]) begin
      $display("packed_array[%0d] = %0h", i, my_array.packed_array[i]);
    end

    $display("Dynamic array values:");
    foreach (my_array.dynamic_array[i]) begin
      $display("dynamic_array[%0d] = %0d", i, my_array.dynamic_array[i]);
    end

    $display("Associative array values:");
    $display("associative_array['key1'] = %0d", my_array.associative_array["key1"]);
    $display("associative_array['key2'] = %0d", my_array.associative_array["key2"]);

    $display("Fixed-size array values:");
    foreach (my_array.fixed_size_array[i]) begin
      $display("fixed_size_array[%0d] = %0h", i, my_array.fixed_size_array[i]);
    end

    $display("Queue array values:");
    foreach (my_array.queue[i]) begin
      $display("queue[%0d] = %0d", i, my_array.queue[i]);
    end

    $finish;
  end

endmodule


