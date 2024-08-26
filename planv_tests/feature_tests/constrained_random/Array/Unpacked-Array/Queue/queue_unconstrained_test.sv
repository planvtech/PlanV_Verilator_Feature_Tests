module queue_unconstrained_test;

  // Queue declaration
  rand int queue_array [$];

  initial begin
    // Initialize the queue with some elements
    queue_array.push_back(0);
    queue_array.push_back(0);

    // Randomization of the queue without constraints
    if (!queue_array.randomize()) begin
      $display("Queue randomization failed.");
    end else begin
      $display("Queue randomization successful.");
    end

    // Displaying the values after randomization
    $display("Queue values:");
    for (int i = 0; i < queue_array.size(); i++) begin
      $display("queue_array[%0d] = %0d", i, queue_array[i]);
    end
  end

endmodule
