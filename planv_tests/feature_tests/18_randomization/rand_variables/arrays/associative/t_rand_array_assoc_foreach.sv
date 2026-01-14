// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: foreach loops in associative array constraints

`include "test_utils.svh"

class constrained_associative_array_foreach;

    rand int int_index_arr [int];
    rand int string_index_arr_2 [string];
    constraint int_index_constraints {
        foreach (int_index_arr[i]) int_index_arr[i] inside {10, 20, 30, 40, 50};
    }

    constraint string_index_2_constraints {
        foreach (string_index_arr_2[i]) string_index_arr_2[i] inside {10, 20, 30, 40, 50}; // nodep->bitp() would be VARREF, instead of CVTPACKSTRING
    }

    // Constructor to initialize arrays
    function new();
        int_index_arr = '{1: 0, 8: 0, 7: 0};
        string_index_arr_2 = '{"key1": 15, "key2": 20, "key3": 30};
    endfunction

    // Function to check and display the arrays
    function void self_check();
        foreach (int_index_arr[i]) begin
            if (!(int_index_arr[i] inside {10, 20, 30, 40, 50})) $stop;
        end
        foreach (string_index_arr_2[i]) begin
            `DBG(("string_index_arr_2[%0s] = %0d", i, string_index_arr_2[i]))
            if (string_index_arr_2[i] < 10) $stop;
        end
    endfunction

endclass

module t_rand_array_assoc_foreach;

  constrained_associative_array_foreach my_1d_array;

  initial begin
    my_1d_array = new();

    // Randomization of the associative arrays with constraints
    if (!my_1d_array.randomize()) begin
      `DBG(("Constrained 1D associative array randomization failed."))
      $stop;
    end

    // Self-checks
    my_1d_array.self_check();

    // Successful execution marker
    `TEST_PASS
  end

endmodule
