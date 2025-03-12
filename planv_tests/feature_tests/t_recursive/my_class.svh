virtual class CallBackBase;
    pure virtual function void add(int a, int b);
endclass : CallBackBase

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
