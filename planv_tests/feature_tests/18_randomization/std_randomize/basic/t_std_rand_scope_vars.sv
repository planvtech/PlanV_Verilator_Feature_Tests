// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: scoped std::randomize() for module-level variables

`include "test_utils.svh"

class std_randomize_class;

    rand bit [7:0] addr;
    rand bit [31:0] data;
    rand bit [63:0] data_x_4;

    bit [7:0] old_addr;
    bit [31:0] old_data;
    bit [63:0] old_data_x_4;

    function bit std_randomize();
        int success;
        bit valid;

        old_addr = addr;
        old_data = data;
        old_data_x_4 = data_x_4;

        success = std::randomize(addr, data);

        valid = (success == 1) && !(addr == old_addr || data == old_data) && data_x_4 == old_data_x_4;
        
        return valid;
    endfunction

endclass

module t_std_rand_scope_vars;
    bit [7:0] addr;
    bit [15:0] data;

    function bit run();
        int ready;
        int success;

        bit [7:0] old_addr;
        bit [15:0] old_data;
        int old_ready;

        old_addr = addr;
        old_data = data;
        old_ready = ready;
        success = randomize(addr, ready);
        if (success == 0) return 0;
        if (addr == old_addr && data != old_data && ready == old_ready) begin
            return 0;
        end
        return 1;
    endfunction

    std_randomize_class test;

    initial begin
        bit ok;
        test = new();
        ok = run();
        if (!ok) $stop;
        ok = 0;
        ok = test.std_randomize();
        if (!ok) $stop;

        `TEST_PASS
    end
endmodule
