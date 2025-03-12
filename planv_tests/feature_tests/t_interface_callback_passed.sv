virtual class CallBackBase;
    pure virtual function void add(int a, int b);
endclass : CallBackBase

interface my_interface;

    CallBackBase callback_obj;

    function void register_callback(CallBackBase obj);
        callback_obj = obj;
    endfunction

    logic clk;
    always @(posedge clk) begin
        if (callback_obj != null)
            callback_obj.add(1, 2);
        else $display("callback_obj is null");
    end
endinterface : my_interface

class my_class extends CallBackBase;
    virtual my_interface vif;

    function new(virtual my_interface vif);
        this.vif = vif;
        $display("my_class::new");
        vif.register_callback(this);
    endfunction

    function void add(int a, int b);
        $display("a + b = %d", a + b);
    endfunction
endclass : my_class

module t_interface_callback_passed;

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
