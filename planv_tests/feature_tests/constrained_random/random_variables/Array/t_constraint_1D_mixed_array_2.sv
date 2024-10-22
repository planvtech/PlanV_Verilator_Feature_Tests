// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

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

  // Self-check function to validate the constraints
  function void check();
    foreach (dynamic_array[i]) begin
      if (dynamic_array[i] < 1 || dynamic_array[i] > 10) begin
        $display("Error: dynamic_array[%0d] = %0d, out of range [1:10]", i, dynamic_array[i]);
        $stop;
      end
    end

    if (associative_array["key1"] < 100 || associative_array["key1"] > 200) begin
      $display("Error: associative_array['key1'] = %0d, out of range [100:200]", associative_array["key1"]);
      $stop;
    end
    if (associative_array["key2"] < 300 || associative_array["key2"] > 400) begin
      $display("Error: associative_array['key2'] = %0d, out of range [300:400]", associative_array["key2"]);
      $stop;
    end

    foreach (fixed_size_array[i]) begin
      if (fixed_size_array[i] != i) begin
        $display("Error: fixed_size_array[%0d] = %0h, expected %0d", i, fixed_size_array[i], i);
        $stop;
      end
    end

    foreach (queue[i]) begin
      if (queue[i] < 50 || queue[i] > 100) begin
        $display("Error: queue[%0d] = %0d, out of range [50:100]", i, queue[i]);
        $stop;
      end
    end
  endfunction

endclass

module t_constraint_1D_mixed_array_2;

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

    // Self-check to validate the randomization
    my_array.check();

    // Additional detailed print information
    $display("Randomization successful!");

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

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
