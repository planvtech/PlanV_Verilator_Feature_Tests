module tb_top;
    import my_pkg::*;

    my_if my_if_inst();

    initial begin
        int result;
        result = my_if_inst.use_add(2, 3);
        $display("result = %d", result);
        $finish;
    end

endmodule
