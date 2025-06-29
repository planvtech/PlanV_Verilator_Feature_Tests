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
    logic s1;
    logic s2;

    INTF vintf();

    assign vintf.x = s1;
    assign vintf.y = '0;
    assign vintf.z = !vintf.y;
    assign s2 = vintf.z;
    assign s1 = s2;

    Dummy d;

    initial begin
        d = new(vintf);
        #1ns;
        $display("x = %0b, y = %0b, z = %0b, s1 = %0b, s2 = %0b, Should be 1, 0, 1, 0, 0. ", d.vif.x, d.vif.y, d.vif.z, s1, s2);
        $finish;
    end
endmodule
