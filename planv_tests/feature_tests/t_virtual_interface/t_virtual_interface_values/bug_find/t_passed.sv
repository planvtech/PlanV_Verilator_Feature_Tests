// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Contact: yilou.wang@planv.tech


`timescale 1ns/1ps

interface INTF();
    logic [7:0] data;
endinterface

module t_passed();
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
        $display("intf1.data = %02x", vif1.data);  // Expected = A5
        $display("data        = %02x", data);
        $display("intf2.data = %02x", vif2.data);

        #1ns;
        if (vif1.data !== 8'hA5) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
    
endmodule
