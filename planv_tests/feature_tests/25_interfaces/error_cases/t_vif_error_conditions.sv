// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: virtual interface error conditions

`include "test_utils.svh"

interface INTF;
    logic x;
    logic y;
    logic z;
endinterface

class Dummy;
    virtual INTF vif;

    function new(virtual INTF vif);
        this.vif = vif;
    endfunction

    function assign_y(logic val);
        vif.y = val;
    endfunction

    function drive_y();
        vif.y = 1;
    endfunction
endclass

module t_vif_error_conditions();
    logic s1, src_val;
    logic s2;
    bit failed;

    INTF vintf();
    INTF vintf_2();

    assign vintf.x = s1;
    assign s1 = vintf.y;
    assign vintf.y = src_val;
    assign vintf.z = vintf.x;

    assign vintf_2.x = vintf.x;
    assign vintf_2.y = s2;
    assign vintf_2.z = vintf.y;

    assign s2 = s1;

    Dummy d;
    Dummy d_2;

    initial begin
        d = new(vintf);
        d_2 = new(vintf_2);

        #5ns;
        // src_val = 1; // Okay, pass, var updated correctly
        // d.assign_y(1); // Failed
        d.drive_y(); // same with assign_y(1)

        #5ns;

        /*
        `DBG(("s1 = %0b, s2 = %0b", s1, s2))
        `DBG(("vintf:  x = %0b, y = %0b, z = %0b", vintf.x, vintf.y, vintf.z))
        `DBG(("vintf_2: x = %0b, y = %0b, z = %0b", vintf_2.x, vintf_2.y, vintf_2.z))

        `DBG(("Dummy vif: x = %0b, y = %0b, z = %0b", d.vif.x, d.vif.y, d.vif.z))
        `DBG(("Dummy vif_2: x = %0b, y = %0b, z = %0b", d_2.vif.x, d_2.vif.y, d_2.vif.z))
        */

        failed = 0;

        if (vintf.y !== 1) begin
            `DBG(("FAIL: vintf.y !== 1"))
            failed = 1;
        end
        if (s1 !== 1) begin
            `DBG(("FAIL: s1 !== 1"))
            failed = 1;
        end
        if (s2 !== 1) begin
            `DBG(("FAIL: s2 !== 1"))
            failed = 1;
        end
        if (vintf_2.y !== 1) begin
            `DBG(("FAIL: vintf_2.y !== 1"))
            failed = 1;
        end
        if (vintf.x !== 1) begin
            `DBG(("FAIL: vintf.x !== 1"))
            failed = 1;
        end
        if (vintf_2.x !== 1) begin
            `DBG(("FAIL: vintf_2.x !== 1"))
            failed = 1;
        end
        if (vintf.z !== 1) begin
            `DBG(("FAIL: vintf.z !== 1"))
            failed = 1;
        end
        if (vintf_2.z !== 1) begin
            `DBG(("FAIL: vintf.z !== 1"))
            failed = 1;
        end

        if (failed) $stop;

        `TEST_PASS
    end
endmodule
