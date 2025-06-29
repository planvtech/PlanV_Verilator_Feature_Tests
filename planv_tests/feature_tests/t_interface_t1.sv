// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

interface INTF();
    logic x;
    logic y;
endinterface

class Driver;
    virtual INTF vif;

    function new(virtual INTF vif);
        this.vif = vif;
    endfunction

    // Reference both fields so Verilator groups them
    task drive();
        if (vif.x == 1)
            vif.y = 1;
        else
            vif.y = 0;
    endtask
endclass

module t_interface_t1;
    logic a, b;

    INTF intf();

    assign intf.x = a;
    assign b = intf.y;
    assign a = b;

    Driver drv;

    initial begin
        b = 1; // 🟢 为 b 赋初值，形成闭环中的唯一值源
        drv = new(intf);
        drv.drive();

        #1ns;
        if (a !== 1 || b !== 1) begin
            $display("FAIL: a = %0b, b = %0b", a, b);
            $stop;
        end

        $display("PASS: a = %0b, b = %0b", a, b);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
