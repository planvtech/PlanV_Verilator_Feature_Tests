// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: virtual interface callback passing between classes

`include "test_utils.svh"

virtual class CallBackBase;
    pure virtual function void add(int a, int b);
endclass : CallBackBase

interface my_interface;

    CallBackBase callback_obj;

    function void register_callback(CallBackBase obj);
        callback_obj = obj;
    endfunction

    logic clk;
endinterface : my_interface

class my_class extends CallBackBase;
    virtual my_interface vif;

    function new(virtual my_interface vif);
        this.vif = vif;
        `DBG(("my_class::new"))
        vif.register_callback(this);
    endfunction

    function void add(int a, int b);
        `DBG(("a + b = %d", a + b))
    endfunction
endclass : my_class

module t_vif_class_callback;

    logic clk = 0;
    my_interface vif();
    my_class cl;

    assign vif.clk = clk;

    initial begin
        forever #5 clk = ~clk;
    end

    initial begin
        #10;
        cl = new(vif);
        #100;
        `TEST_PASS
    end
endmodule : t_vif_class_callback
