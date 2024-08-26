module queue_constrained_test;

  // Queue declaration
  rand int queue_array [$];

  // Constraints
  constraint queue_array_constraints {
    queue_array.size() == 3;  // Fixing the size of the queue
    queue_array[0] == 10;
    queue_array[1] inside {20, 30, 40};
    queue_array[2] < 100;
  }

  initial begin
    // Initialize the queue with some elements
    queue_array.push_back(0);
    queue_array.push_back(0);
    queue_array.push_back(0);

    // Randomization of the queue with constraints
    if (!this.randomize() with {queue_array_constraints}) begin
      $display("Constrained queue randomization failed.");
    end else begin
      $display("Constrained queue randomization successful.");
    end

    // Displaying the values after randomization
    $display("Queue values:");
    for (int i = 0; i < queue_array.size(); i++) begin
      $display("queue_array[%0d] = %0d", i, queue_array[i]);
    end
  end

endmodule
