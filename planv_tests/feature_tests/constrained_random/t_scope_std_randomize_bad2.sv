module t_scope_std_randomize_bad2;
    bit [3:0] a;

    function bit run();
        bit success;
        success = std::randomize(a + 1); // ❌ ERROR: argument is not a variable
        $display("a=%0h", a);
        return success;
    endfunction

    initial begin
        bit ok;
        ok = run();
        $display("ok=%0d", ok);
        if (!ok) $stop;
    end
endmodule
