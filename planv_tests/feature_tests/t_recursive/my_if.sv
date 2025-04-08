interface my_interface;
    import my_pkg::*;
    CallBackBase callback_obj;

    function void register_callback(CallBackBase obj);
        $display("my_interface::register_callback");
        callback_obj = obj;
    endfunction

    logic clk;
    always @(posedge clk) begin
        $display("my_interface::always");
        if (callback_obj != null)
            callback_obj.add(callback_obj.a, callback_obj.b);
        else $display("callback_obj is null");
    end
endinterface : my_interface
