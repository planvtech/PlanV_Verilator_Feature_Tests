module t_scope_std_randomize_bad3;
    bit [3:0] a;

    function void define();
        bit b;
    endfunction

    function bit run();
        bit success;
        success = std::randomize(a, b); // ❌ ERROR: addr is not declared in current scope
        $display("a=%0h", a);
        $display("b=%0h", b);
        return success;
    endfunction

    initial begin
        bit ok;
        ok = run();
        $display("ok=%0d", ok);
        if (!ok) $stop;
    end
endmodule
