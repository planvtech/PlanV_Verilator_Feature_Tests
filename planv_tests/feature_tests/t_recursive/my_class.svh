virtual class CallBackBase;
    pure virtual function void add(int a, int b);
    int a, b;
endclass : CallBackBase

class my_class extends CallBackBase;
    virtual my_interface vif;

    function new(virtual my_interface vif);
        this.vif = vif;
        $display("my_class::new");
        vif.register_callback(this);
    endfunction

    function void add(int a, int b);
        $display("my_class::add");
        $display("a + b = %d", a + b);
        run();
    endfunction

    task run();
        $display("my_class::run");
        repeat(3) begin
            #10;
            a = $random;
            b = $random;
        end
    endtask

endclass : my_class
