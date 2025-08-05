class Sub;
    rand bit [3:0] val;
    constraint c1 { val == 4; }
endclass

class Top;
    rand Sub obj;
    function new();
        obj = new();
    endfunction
endclass

module t_global_rand_t1;
    Top t = new();
    initial begin
        if (!t.randomize()) $stop;
        $display("T1: obj.val = %0d", t.obj.val);
        if (t.obj.val !== 4) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule