// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: virtual interface test passing case

`include "test_utils.svh"

`timescale 1ns/1ps

interface INTF();
    logic [7:0] data;
endinterface

module t_vif_values_valid();
    logic [7:0] data;

    INTF intf1();
    INTF intf2();

    assign intf1.data = data;
    assign data = intf2.data;

    virtual INTF vif1;
    virtual INTF vif2;

    initial begin
        vif1 = intf1;
        vif2 = intf2;

        vif2.data = 8'hA5;

        #1ns;
        `DBG(("intf1.data = %02x", vif1.data))  // Expected = A5
        `DBG(("data        = %02x", data))
        `DBG(("intf2.data = %02x", vif2.data))

        #1ns;
        if (vif1.data !== 8'hA5) $stop;

        `TEST_PASS
    end
    
endmodule
