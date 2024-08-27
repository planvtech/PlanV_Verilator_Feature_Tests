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
    dynamic_array.size() == 5;
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
    queue.size() == 2;
    queue[0] inside {[50:60]};
    queue[1] inside {[70:80]};
  }

endclass

module mixed_array_constrained_test_no_foreach;

  constrained_mixed_array my_array;

  initial begin
    my_array = new();
    
    my_array.dynamic_array = new[5];
    my_array.associative_array["key1"] = 0;
    my_array.associative_array["key2"] = 0;
    my_array.queue.push_back(0);
    my_array.queue.push_back(0);

    if (!my_array.randomize()) begin
      $display("Constrained mixed array randomization failed.");
      $stop;
    end

    $display("Packed array values:");
    $display("packed_array = %0h", my_array.packed_array);

    $display("Unpacked array values:");
    for (int i = 0; i < 4; i++) begin
      $display("unpacked_array[%0d] = %0b", i, my_array.unpacked_array[i]);
    end

    $display("Dynamic array values:");
    for (int i = 0; i < 5; i++) begin
      $display("dynamic_array[%0d] = %0d", i, my_array.dynamic_array[i]);
    end

    $display("Associative array values:");
    $display("associative_array['key1'] = %0d", my_array.associative_array["key1"]);
    $display("associative_array['key2'] = %0d", my_array.associative_array["key2"]);

    $display("Fixed-size array values:");
    for (int i = 0; i < 4; i++) begin
      $display("fixed_size_array[%0d] = %0h", i, my_array.fixed_size_array[i]);
    end

    $display("Queue array values:");
    for (int i = 0; i < my_array.queue.size(); i++) begin
      $display("queue[%0d] = %0d", i, my_array.queue[i]);
    end

    $finish;
  end

endmodule

