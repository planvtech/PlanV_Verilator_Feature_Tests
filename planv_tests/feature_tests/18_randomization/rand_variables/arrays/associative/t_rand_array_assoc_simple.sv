// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: rand associative array randomization

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

class array;

    rand int assoc_arr[string][string];

    function new();
      assoc_arr["John"]["Math"] = 85;
      assoc_arr["John"]["Science"] = 90;
      assoc_arr["Alice"]["Math"] = 75;
      assoc_arr["Alice"]["Science"] = 80;
    endfunction

    // Self-check function to validate randomization
    function void check();
      `check_rand(this, this.assoc_arr["John"]["Math"]);
      `check_rand(this, this.assoc_arr["John"]["Science"]);
      `check_rand(this, this.assoc_arr["Alice"]["Math"]);
      `check_rand(this, this.assoc_arr["Alice"]["Science"]);
    endfunction

    task display_assoc_array();
      // Display the entire associative array content
      `DBG(("John - Math: %0d, Science: %0d", assoc_arr["John"]["Math"], assoc_arr["John"]["Science"]))
      `DBG(("Alice - Math: %0d, Science: %0d", assoc_arr["Alice"]["Math"], assoc_arr["Alice"]["Science"]))
    endtask
endclass

module t_rand_array_assoc_simple;

    array cl;

  initial begin
    cl = new();

    `DBG(("Associative Array Content before rand:"))
    cl.display_assoc_array();

    `DBG(("Associative Array Check Rand:"))
    cl.check();

    `DBG(("Associative Array Content after rand:"))
    cl.display_assoc_array();

    `TEST_PASS
  end

endmodule
