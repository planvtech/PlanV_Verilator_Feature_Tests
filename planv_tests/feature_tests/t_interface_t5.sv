`timescale 1ns/1ps

interface INTF();
    logic clk;
    logic [7:0] data;
    logic valid;
    logic ready;
endinterface

time TA = 1ns; // application time

class intf_driver;
    virtual INTF intf;
    function new(virtual INTF intf);
        this.intf = intf;
    endfunction

    task cycle_start();
        #TA;
    endtask

    task cycle_end();
        @(posedge intf.clk);
    endtask

    task init_master();
        intf.data = '0;
        intf.valid = 0;
    endtask

    task init_slave();
        intf.ready = 0;
    endtask

    task recv_data(output logic [7:0] data);
        intf.ready <= #TA 1;
        cycle_start();
        while (intf.valid != 1) begin cycle_end(); cycle_start(); end
        cycle_end();
        data = intf.data;
        intf.ready <= #TA 0;
    endtask

    task send_data(input logic [7:0] data);
        intf.data <= #TA data;
        intf.valid <= #TA 1;
        cycle_start();
        while (intf.ready != 1) begin cycle_end(); cycle_start(); end
        cycle_end();
        intf.valid <= #TA 0;
    endtask
endclass

module t_interface_t5();
    logic clk;
    logic [7:0] data;
    logic valid;
    logic ready;

    INTF read_intf();
    assign read_intf.clk = clk;
    assign read_intf.data = data;
    assign read_intf.valid = valid;
    assign ready = read_intf.ready;

    INTF write_intf();
    assign write_intf.clk = clk;
    assign data = write_intf.data;
    assign valid = write_intf.valid;
    assign write_intf.ready = ready;

    intf_driver driver_master;
    intf_driver driver_slave;

    initial begin
        forever begin
            clk = '1;
            #10ns;
            clk = '0;
            #10ns;
        end
    end

    initial begin
        driver_master = new(write_intf);
        driver_master.init_master();

        #32ns;
        driver_master.send_data(8'h42);
    end

    logic [7:0] recv_data;
    initial begin
        driver_slave = new(read_intf);
        driver_slave.init_slave();

        #22ns;
        driver_slave.recv_data(recv_data);

        $display("Got data: %02x", recv_data);
        $finish;
    end
endmodule
