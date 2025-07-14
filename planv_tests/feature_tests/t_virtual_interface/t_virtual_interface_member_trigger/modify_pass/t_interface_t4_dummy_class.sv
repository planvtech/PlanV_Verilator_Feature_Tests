// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


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
endclass

module t_interface_t4_dummy_class();
    logic s1, src_val;
    logic s2;

    INTF vintf();

    assign vintf.x = s1;
    assign vintf.y = src_val;
    assign vintf.z = !vintf.y;
    assign s2 = vintf.z;
    assign s1 = s2;

    Dummy d;

    initial begin
        d = new(vintf);
        #1ns;
        src_val = 0;
        #1ns;
        if (!(d.vif.x == 1 && d.vif.y == 0 && d.vif.z == 1 && s1 == 1 && s2 == 1)) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
