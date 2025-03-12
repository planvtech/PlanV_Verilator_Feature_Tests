module t_interface_callback_passed;
    import my_pkg::*;
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
        $finish;
    end
endmodule : t_interface_callback_passed
