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
    logic a = 1;
    logic b;

    INTF intf();

    assign intf.x = a;
    assign b = intf.y;
    assign a = b;

    Driver drv;

    initial begin
        drv = new(intf);
        drv.drive();

        // If scheduling works, a and b will stabilize to 1
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
