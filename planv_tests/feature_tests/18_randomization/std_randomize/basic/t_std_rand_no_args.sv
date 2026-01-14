// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: std::randomize() with no arguments

`include "test_utils.svh"

module t_std_rand_no_args;
    bit [7:0] addr;
    bit [15:0] data;
    bit [7:0] old_addr;
    bit [15:0] old_data;

    initial begin
        old_addr = addr;
        old_data = data;

        if (!std::randomize()) $stop;

        // check if values changed
        if (!(addr == old_addr && data == old_data)) $stop;

        `TEST_PASS
    end
endmodule
