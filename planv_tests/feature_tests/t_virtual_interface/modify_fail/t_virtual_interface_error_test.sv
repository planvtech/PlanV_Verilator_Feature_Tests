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

module t_virtual_interface_error_test();
    logic s1, src_val;
    logic s2;
    bit failed;

    INTF vintf();
    INTF vintf_2();

    assign vintf.x = s1;
    assign s1 = vintf.y;
    assign vintf.y = src_val;

    assign vintf_2.x = vintf.x;
    assign vintf_2.y = s2;
    assign vintf_2.z = vintf.y;

    assign s2 = s1;

    Dummy d;
    Dummy d_2;

    initial begin
        d = new(vintf);
        d_2 = new(vintf_2);

        #1ns;
        // src_val = 1; // Okay, pass, var updated correctly
        // d.assign_y(1); // Not okay, only d's interface change, local var s1 changes, but d_2's interface does not change
        d.drive_y(); // same with assign_y(1)

        #5ns;

        $display("s1 = %0b, s2 = %0b", s1, s2);
        $display("vintf:  x = %0b, y = %0b, z = %0b", vintf.x, vintf.y, vintf.z);
        $display("vintf_2: x = %0b, y = %0b, z = %0b", vintf_2.x, vintf_2.y, vintf_2.z);

        $display("Dummy vif: x = %0b, y = %0b, z = %0b", d.vif.x, d.vif.y, d.vif.z);
        $display("Dummy vif_2: x = %0b, y = %0b, z = %0b", d_2.vif.x, d_2.vif.y, d_2.vif.z);

        failed = 0;

        if (vintf.y !== 1) begin
            $display("FAIL: vintf.y !== 1");
            failed = 1;
        end
        if (s1 !== 1) begin
            $display("FAIL: s1 !== 1");
            failed = 1;
        end
        if (s2 !== 1) begin
            $display("FAIL: s2 !== 1");
            failed = 1;
        end
        if (vintf_2.y !== 1) begin
            $display("FAIL: vintf_2.y !== 1");
            failed = 1;
        end
        if (vintf.x !== 1) begin
            $display("FAIL: vintf.x !== 1");
            failed = 1;
        end
        if (vintf_2.x !== 1) begin
            $display("FAIL: vintf_2.x !== 1");
            failed = 1;
        end

        if (failed) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
