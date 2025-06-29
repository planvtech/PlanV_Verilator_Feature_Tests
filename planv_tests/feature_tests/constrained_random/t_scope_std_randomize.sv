module t_scope_std_randomize;
    bit [7:0] addr;
    bit [15:0] data;

    function bit run();
        int ready;
        run = std::randomize(addr, data, ready); // correct: all variables in local/module scope
        $display("addr=%0h, data=%0h, ready=%0d", addr, data, ready);
        return run;
    endfunction

    initial begin
        bit ok;
        ok = run();
        $display("ok=%0d", ok);
        if (!ok) $stop;
    end
endmodule
