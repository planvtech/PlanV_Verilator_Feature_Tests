// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: rand queue randomization

`include "test_utils.svh"

`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) begin \
      `DBG(("Error: Randomization failed for %s", field)) \
      $stop; \
   end \
end

class unconstrained_queue;

  rand int queue [$];
  rand int queue_2d[$][$];

  // Function to use check_rand macro for validation
  function void check();
    foreach (queue[i]) begin
      `check_rand(this, queue[i]);
    end

    foreach (queue_2d[i, j]) begin
      `check_rand(this, queue_2d[i][j]);
    end
  endfunction

endclass

module t_rand_array_queue_simple;

  unconstrained_queue my_queue;

  initial begin
    my_queue = new();

    // Initialize the queue with some elements
    my_queue.queue.push_back(0);
    my_queue.queue.push_back(0);

    // Initialize the 2D queue with some elements
    my_queue.queue_2d.push_back('{1, 2});
    my_queue.queue_2d.push_back('{3, 4});

    // Randomization of the queue without constraints
    if (!my_queue.randomize()) begin
      `DBG(("Queue randomization failed."))
      $stop;
    end

    // Self-check to validate the randomization using check_rand
    my_queue.check();

    // Displaying the values after randomization
    `DBG(("Queue values:"))
    for (int i = 0; i < my_queue.queue.size(); i++) begin
      `DBG(("queue[%0d] = %0d", i, my_queue.queue[i]))
    end

    `DBG(("2D Queue values:"))
    for (int i = 0; i < my_queue.queue_2d.size(); i++) begin
      for (int j = 0; j < my_queue.queue_2d[i].size(); j++) begin
        `DBG(("queue_2d[%0d][%0d] = %0d", i, j, my_queue.queue_2d[i][j]))
      end
    end

    // Successful execution marker
    `TEST_PASS
  end

endmodule
