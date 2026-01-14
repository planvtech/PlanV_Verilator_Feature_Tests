// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: basic timing delay operators (#delay)

`include "test_utils.svh"

module t_timing_basic_delay;
    int counter = 0;

    initial begin
        `DBG(("[%0t] Starting test", $time))
        counter = 1;
        #100ns;
        `DBG(("[%0t] After 100ns delay, counter=%0d", $time, counter))
        counter = 2;
        #200ns;
        `DBG(("[%0t] After 200ns delay, counter=%0d", $time, counter))
        // Check that time advanced (don't assume specific time unit)
        if ($time >= 300) begin
            `TEST_PASS
        end else begin
            $error("Time did not advance correctly: $time=%0t", $time);
            $stop;
        end
    end
endmodule
