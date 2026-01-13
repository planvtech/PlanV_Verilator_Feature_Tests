class Sub_sub;
    rand bit [3:0] val;
    constraint c { val == 3; }
    function new();
        val = 0; // Initialize to 0
    endfunction
endclass

class Sub;
    rand Sub_sub inner;
    rand bit [3:0] val;
    constraint c { val > 4; }
    function new();
        inner = new();
        val = 0;
    endfunction
endclass

class Top;
    rand Sub obj;
    rand bit [3:0] val;
    constraint c { obj.val == 5; }
    function new();
        obj = new();
        val = 0; // Initialize to 0
    endfunction
endclass

module t_global_rand_t1;
    int success;
    Top t = new();
    initial begin
        success = t.randomize();
        if (success != 1) $stop;
        
        $display("T1: val = %0d, obj.val = %0d, obj.inner.val = %0d", t.val, t.obj.val, t.obj.inner.val);
 
        if (t.obj.val !== 5) $stop;
        if (t.obj.inner.val !== 3) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
