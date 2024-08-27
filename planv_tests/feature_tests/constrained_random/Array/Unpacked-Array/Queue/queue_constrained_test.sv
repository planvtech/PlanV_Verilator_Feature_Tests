class constrained_queue_array;

  rand int queue_array [$];

  // Constraints
  constraint queue_array_constraints {
    queue_array.size() == 3;  // Fixing the size of the queue
    queue_array[0] == 10;
    queue_array[1] inside {20, 30, 40};
    queue_array[2] < 100;
  }

endclass

module queue_constrained_test;

  constrained_queue_array my_queue;

  initial begin
    my_queue = new();

    // Initialize the queue with some elements
    my_queue.queue_array.push_back(0);
    my_queue.queue_array.push_back(0);
    my_queue.queue_array.push_back(0);

    // Randomization of the queue with constraints
    if (!my_queue.randomize()) begin
      $display("Constrained queue randomization failed.");
      $stop;
    end

    // Displaying the values after randomization
    $display("Queue values:");
    for (int i = 0; i < my_queue.queue_array.size(); i++) begin
      $display("queue_array[%0d] = %0d", i, my_queue.queue_array[i]);
    end

    $finish;
  end

endmodule
