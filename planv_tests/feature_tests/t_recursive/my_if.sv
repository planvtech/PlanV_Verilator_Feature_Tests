interface my_interface;
    import my_pkg::*;
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
