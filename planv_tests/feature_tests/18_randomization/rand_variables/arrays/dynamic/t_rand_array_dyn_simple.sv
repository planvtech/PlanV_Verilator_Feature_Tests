// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: rand dynamic array randomization (1D only)
//
// NOTE: QuestaSim crashes (SIGSEGV) when randomizing multi-dimensional dynamic arrays
// This test is simplified to only test 1D dynamic arrays

`include "test_utils.svh"

class dynamic_arrays;

    rand int dynamic_array_1d[]; // 1D dynamic array

    function new();
        // Initialize 1D dynamic array with size 5
        dynamic_array_1d = new[5];
    endfunction

    // Simple check: verify array has expected size after randomization
    function void check();
        // Check 1D array size
        if (dynamic_array_1d.size() != 5) begin
            `DBG(("Error: dynamic_array_1d size mismatch"))
            $stop;
        end
    endfunction

endclass

module t_rand_array_dyn_simple;

  dynamic_arrays cl;

  initial begin
    cl = new();

    // Randomization of dynamic array
    if (!cl.randomize()) begin
      `DBG(("Dynamic array randomization failed."))
      $stop;
    end

    // Self-check to validate size preserved
    cl.check();

    `DBG(("1D Dynamic array values:"))
    for (int i = 0; i < cl.dynamic_array_1d.size(); i++) begin
      `DBG(("dynamic_array_1d[%0d] = %0d", i, cl.dynamic_array_1d[i]))
    end

    // Successful execution marker
    `TEST_PASS
  end

endmodule
