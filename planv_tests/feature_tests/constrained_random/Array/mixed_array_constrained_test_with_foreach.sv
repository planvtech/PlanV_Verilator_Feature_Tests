class constrained_mixed_array;

  rand int dynamic_array [];
  rand int associative_array [string];
  rand bit [7:0] fixed_size_array [4];
  rand int queue [$];

  // Constraints

  constraint dynamic_array_constraints {
    dynamic_array.size() == 5;
    foreach(dynamic_array[i]) dynamic_array[i] inside {[1:10]};
  }

  constraint associative_array_constraints {
    associative_array["key1"] inside {[100:200]};
    associative_array["key2"] inside {[300:400]};
  }

  constraint fixed_size_array_constraints {
    foreach(fixed_size_array[i]) fixed_size_array[i] == i;
  }

  constraint queue_constraints {
    foreach(queue[i]) queue[i] inside {[50:100]};
  }

endclass

module mixed_array_constrained_test_with_foreach;

  constrained_mixed_array my_array;

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

    if (!my_array.randomize()) begin
      $display("Constrained mixed array randomization failed.");
      $stop;
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
