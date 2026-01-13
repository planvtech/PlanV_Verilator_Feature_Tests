// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class constrained_mixed_array;

  rand bit [7:0] packed_array;
  rand bit unpacked_array [4];
  rand int dynamic_array [];
  rand int associative_array [string];
  rand bit [7:0] fixed_size_array [4];
  rand int queue [$];

  // Constraints for each array
  constraint packed_array_constraints {
    packed_array == 8'hAA;
  }

  constraint unpacked_array_constraints {
    unpacked_array[0] inside {1'b1};
    unpacked_array[1] inside {1'b1};
    unpacked_array[2] == 1'b0;
  }

  constraint dynamic_array_constraints {
    dynamic_array.size == 5;
    dynamic_array[0] == 1;
    dynamic_array[1] == 2;
    dynamic_array[2] == 3;
    dynamic_array[3] == 4;
    dynamic_array[4] == 5;
  }

  constraint associative_array_constraints {
    associative_array["key1"] == 100;
    associative_array["key2"] == 200;
  }

  constraint fixed_size_array_constraints {
    fixed_size_array[0] == 8'h01;
    fixed_size_array[1] == 8'h02;
    fixed_size_array[2] == 8'h03;
    fixed_size_array[3] == 8'h04;
  }

  constraint queue_constraints {
    queue.size == 2;
    queue[0] inside {[50:60]};
    queue[1] inside {[70:80]};
  }

  // Check function to self-validate the randomization
  function void check();
    $display("Checking arrays for constraint compliance:");

    // Check packed array
    if (packed_array != 8'hAA) begin
      $display("Error: packed_array = %0h, expected = 8'hAA", packed_array);
      $stop;
    end else begin
      $display("Packed array meets constraint: packed_array = %0h", packed_array);
    end

    // Check unpacked array
    if (unpacked_array[0] != 1'b1 || unpacked_array[1] != 1'b1 || unpacked_array[2] != 1'b0) begin
      $display("Error: unpacked_array does not match constraint.");
      $stop;
    end else begin
      for (int i = 0; i < 4; i++) begin
        $display("unpacked_array[%0d] = %0b", i, unpacked_array[i]);
      end
    end

    // Check dynamic array
    for (int i = 0; i < dynamic_array.size(); i++) begin
      if (dynamic_array[i] != i + 1) begin
        $display("Error: dynamic_array[%0d] = %0d, expected = %0d", i, dynamic_array[i], i + 1);
        $stop;
      end
    end
    $display("Dynamic array meets constraint: %p", dynamic_array);

    // Check associative array
    if (associative_array["key1"] != 100 || associative_array["key2"] != 200) begin
      $display("Error: associative_array does not match constraint.");
      $stop;
    end else begin
      $display("associative_array['key1'] = %0d", associative_array["key1"]);
      $display("associative_array['key2'] = %0d", associative_array["key2"]);
    end

    // Check fixed size array
    for (int i = 0; i < 4; i++) begin
      if (fixed_size_array[i] != i + 1) begin
        $display("Error: fixed_size_array[%0d] = %0h, expected = %0h", i, fixed_size_array[i], i + 1);
        $stop;
      end
    end
    $display("Fixed size array meets constraint: %p", fixed_size_array);

    // Check queue
    if (queue.size() != 2 || queue[0] < 50 || queue[0] > 60 || queue[1] < 70 || queue[1] > 80) begin
      $display("Error: queue does not match constraint.");
      $stop;
    end else begin
      for (int i = 0; i < queue.size(); i++) begin
        $display("queue[%0d] = %0d", i, queue[i]);
      end
    end
  endfunction

endclass

module t_constraint_1D_mixed_array_1;

  constrained_mixed_array my_array;

  initial begin
    my_array = new();
    
    // Initialize dynamic array, associative array and queue
    my_array.dynamic_array = new[5];
    my_array.associative_array["key1"] = 0;
    my_array.associative_array["key2"] = 0;
    my_array.queue.push_back(0);
    my_array.queue.push_back(0);

    if (!my_array.randomize()) begin
      $display("Constrained mixed array randomization failed.");
      $stop;
    end

    // Self-check to ensure constraints are met
    my_array.check();

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
