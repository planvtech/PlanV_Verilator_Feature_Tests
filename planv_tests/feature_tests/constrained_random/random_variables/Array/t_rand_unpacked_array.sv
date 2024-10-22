// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

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
      $display("Error: Randomization failed for %s", `"field"`); \
      $stop; \
   end \
end

class unconstrained_unpacked_array;

  rand int unpacked_array [3];
  
  // Function to check randomization using check_rand
  function void check();
    foreach (unpacked_array[i]) begin
      `check_rand(this, this.unpacked_array[i]);
    end
  endfunction

endclass

module t_rand_unpacked_array;

  unconstrained_unpacked_array my_array;

  initial begin
    my_array = new();

    // Randomization of the unpacked array without constraints
    if (!my_array.randomize()) begin
      $display("Unpacked array randomization failed.");
      $stop;
    end

    // Self-check using check_rand macro
    my_array.check();

    // Displaying the values after randomization
    $display("Unpacked array values:");
    for (int i = 0; i < 3; i++) begin
      $display("unpacked_array[%0d] = %0d", i, my_array.unpacked_array[i]);
    end

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
