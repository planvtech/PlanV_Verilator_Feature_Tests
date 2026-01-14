// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: basic constraints on dynamic arrays and queues
//
// NOTE: Simplified to avoid QuestaSim SIGFPE crash with complex mixed queue/dynamic arrays

`include "test_utils.svh"

// Test 1: Simple 1D queue with constraints
class SimpleQueue1D;
    rand int queue_1d[$];

    constraint queue_constraints {
        foreach (queue_1d[i]) queue_1d[i] == i + 2;
    }

    function new();
        queue_1d = {1, 2, 3, 4};
    endfunction

    function void check();
        foreach (queue_1d[i]) begin
            if (queue_1d[i] != i + 2) begin
                `DBG(("Error: queue_1d[%0d] = %0d does not meet constraint", i, queue_1d[i]))
                $stop;
            end
        end
    endfunction
endclass

// Test 2: Simple 2D dynamic array with constraints
class SimpleDyn2D;
    rand int dyn[][];

    constraint dyn_constraints {
        dyn[0][0] == 10;
        dyn[1][0] inside {20, 30, 40};
        dyn[0][1] < 100;
    }

    function new();
        dyn = new[2];
        dyn[0] = new[2];
        dyn[1] = new[2];
    endfunction

    function void check();
        if (dyn[0][0] != 10) begin
            `DBG(("Error: dyn[0][0] != 10"))
            $stop;
        end
        if (!(dyn[1][0] inside {20, 30, 40})) begin
            `DBG(("Error: dyn[1][0] not in {20, 30, 40}"))
            $stop;
        end
        if (dyn[0][1] >= 100) begin
            `DBG(("Error: dyn[0][1] >= 100"))
            $stop;
        end
    endfunction
endclass

// Test 3: Unpacked array of queues
class UnpackedQueue;
    rand int unp_queue[3][$];

    constraint unp_queue_constraints {
        foreach (unp_queue[i, j]) unp_queue[i][j] == (i * 5) + j + 1;
    }

    function new();
        unp_queue[0] = {17, 18};
        unp_queue[1] = {19};
        unp_queue[2] = {20};
    endfunction

    function void check();
        if (unp_queue[0][0] != 1) begin
            `DBG(("Error: unp_queue[0][0] = %0d, expected 1", unp_queue[0][0]))
            $stop;
        end
        if (unp_queue[0][1] != 2) begin
            `DBG(("Error: unp_queue[0][1] = %0d, expected 2", unp_queue[0][1]))
            $stop;
        end
        if (unp_queue[1][0] != 6) begin
            `DBG(("Error: unp_queue[1][0] = %0d, expected 6", unp_queue[1][0]))
            $stop;
        end
        if (unp_queue[2][0] != 11) begin
            `DBG(("Error: unp_queue[2][0] = %0d, expected 11", unp_queue[2][0]))
            $stop;
        end
    endfunction
endclass

module t_rand_array_queue_dyn;
    SimpleQueue1D queue_test;
    SimpleDyn2D dyn_test;
    UnpackedQueue unp_test;
    int success;

    initial begin
        `DBG(("Test: Randomization for queues and dynamic arrays:"))

        // Test 1: Simple 1D queue
        queue_test = new();
        success = queue_test.randomize();
        if (success != 1) begin
            `DBG(("SimpleQueue1D randomization failed."))
            $stop;
        end
        queue_test.check();
        `DBG(("SimpleQueue1D: PASSED"))

        // Test 2: Simple 2D dynamic array
        dyn_test = new();
        success = dyn_test.randomize();
        if (success != 1) begin
            `DBG(("SimpleDyn2D randomization failed."))
            $stop;
        end
        dyn_test.check();
        `DBG(("SimpleDyn2D: PASSED"))

        // Test 3: Unpacked array of queues
        unp_test = new();
        success = unp_test.randomize();
        if (success != 1) begin
            `DBG(("UnpackedQueue randomization failed."))
            $stop;
        end
        unp_test.check();
        `DBG(("UnpackedQueue: PASSED"))

        `TEST_PASS
    end
endmodule
