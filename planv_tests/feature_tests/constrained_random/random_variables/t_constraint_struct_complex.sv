
typedef struct {
  rand int value;
} my_struct_t;

class struct_array_test;
  rand my_struct_t struct_array[10];

  // Constraint: value in range [0, 100]
  constraint struct_c {
    foreach (struct_array[i]) {
      struct_array[i].value inside {[0:100]};
    }
  }

  // Display the randomized array
  function void display();
    $display("Randomized struct array:");
    foreach (struct_array[i]) begin
      $display("  struct_array[%0d].value = %0d", i, struct_array[i].value);
    end
  endfunction

  // Self-test to validate constraints
  function void self_test();
    foreach (struct_array[i]) begin
      if (struct_array[i].value < 0 || struct_array[i].value > 100) begin
        $display("ERROR: struct_array[%0d].value = %0d out of bounds!", 
                 i, struct_array[i].value);
        $stop;
      end
    end
  endfunction
endclass

module test;

  int success;
  struct_array_test test_obj;

  initial begin
    test_obj = new();
    success = test_obj.randomize();

    if (success != 1) begin
      $display("ERROR: Randomization failed!");
      $stop;
    end

    test_obj.display();
    test_obj.self_test();

    $display("TEST PASSED.");
    $finish;
  end
endmodule
