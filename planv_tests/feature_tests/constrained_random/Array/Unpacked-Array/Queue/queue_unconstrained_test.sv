class unconstrained_queue_array;

  rand int queue_array [$];

endclass

module queue_unconstrained_test;

  unconstrained_queue_array my_queue;

  initial begin
    my_queue = new();

    // Initialize the queue with some elements
    my_queue.queue_array.push_back(0);
    my_queue.queue_array.push_back(0);

    // Randomization of the queue without constraints
    if (!my_queue.randomize()) begin
      $display("Queue randomization failed.");
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
