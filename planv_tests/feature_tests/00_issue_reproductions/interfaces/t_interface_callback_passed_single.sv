// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: virtual interface callback passing between classes

// Package containing class definitions
`include "test_utils.svh"

package my_pkg;
    // Virtual base class for callback
    virtual class CallBackBase;
        pure virtual function void add(int a, int b);
        int a, b;
    endclass : CallBackBase

    // Derived class implementing callback
    class my_class extends CallBackBase;
        virtual my_interface vif;

        function new(virtual my_interface vif);
            this.vif = vif;
            `DBG(("my_class::new"))
            vif.register_callback(this);
        endfunction

        function void add(int a, int b);
            `DBG(("my_class::add"))
            `DBG(("a + b = %d", a + b))
            run();
        endfunction

        task run();
            `DBG(("my_class::run"))
            repeat(3) begin
                #10;
                a = $random;
                b = $random;
            end
        endtask
    endclass : my_class
endpackage

// Interface definition
interface my_interface;
    import my_pkg::*;
    CallBackBase callback_obj;

    function void register_callback(CallBackBase obj);
        `DBG(("my_interface::register_callback"))
        callback_obj = obj;
    endfunction

    logic clk;
    always @(posedge clk) begin
        `DBG(("my_interface::always"))
        if (callback_obj != null)
            callback_obj.add(callback_obj.a, callback_obj.b);
        else `DBG(("callback_obj is null"))
    end
endinterface : my_interface

// Top-level test module
module t_interface_callback_passed_merged;
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
endmodule : t_interface_callback_passed_merged
