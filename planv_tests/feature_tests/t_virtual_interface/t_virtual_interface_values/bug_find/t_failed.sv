// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Contact: yilou.wang@planv.tech

`timescale 1ns/1ps

interface INTF();
    logic [7:0] data;
endinterface

class Writer;
    virtual INTF vif;
    function new(virtual INTF vif);
        this.vif = vif;
    endfunction

    task write_data(logic [7:0] d);
        vif.data = d;
    endtask
endclass

module t_failed();
    logic [7:0] data;

    INTF intf_read();
    INTF intf_write();

    assign intf_read.data = data;
    assign data = intf_write.data;

    virtual INTF vif_read, vif_write;
    Writer writer;

    initial begin
        #1ns;
        vif_write = intf_write;
        vif_read  = intf_read;

        #1ns;
        vif_write.data = 8'hA5;

        #1ns;
        $display("vif_write.data  = %02x", vif_write.data); // Expected = A5
        $display("intf_write.data = %02x", intf_write.data);
        $display("module.data     = %02x", data);
        $display("intf_read.data  = %02x", intf_read.data);
        $display("vif_read.data   = %02x", vif_read.data);

        #1ns;
        if (vif_read.data !== 8'hA5) $stop;

        #1ns;
        writer = new(vif_write);
        #1ns;
        writer.write_data(8'hB7);

        #1ns;
        $display("vif_write.data  = %02x", vif_write.data); // Expected = B7
        $display("intf_write.data = %02x", intf_write.data);
        $display("module.data     = %02x", data);
        $display("intf_read.data  = %02x", intf_read.data); // Unexpected Bug Here
        $display("vif_read.data   = %02x", vif_read.data);  // Unexpected Bug Here

        if (vif_read.data !== 8'hB7) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
    
endmodule
