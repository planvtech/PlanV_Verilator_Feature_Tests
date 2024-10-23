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
      $display("Error: Randomization failed for %s", field); \
      $stop; \
   end \
end

class unconstrained_packed_array;

    rand bit [2:0] [15:0] packed_array; // 3 16-bits

    // Function to use check_rand macro for validation
    function void check();
      foreach (packed_array[i]) begin
        `check_rand(this, packed_array[i]);
      end
    endfunction

endclass

module t_rand_packed_array;

  unconstrained_packed_array my_array;

  initial begin
    my_array = new();
    if (!my_array.randomize()) begin
      $display("Packed array randomization failed.");
      $stop;
    end

    // Self-check to validate the randomization using check_rand
    my_array.check();

    // Detailed print information
    $display("Packed array values:");
    for (int i = 0; i < 3; i++) begin
      $display("packed_array[%0d] = %0h", i, my_array.packed_array[i]);
    end

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
