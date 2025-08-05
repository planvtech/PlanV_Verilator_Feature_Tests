class Sub;
    int limit; 
    rand bit [3:0] val;
    constraint c1 { val == limit; }

    function new(int x);
        limit = x;
    endfunction
endclass

class Top;
    rand Sub obj1;
    rand Sub obj2;
    function new();
        obj1 = new(2);
        obj2 = new(5);
    endfunction
endclass

module t_global_rand_t2;
    Top t = new();
    initial begin
        if (!t.randomize()) $stop;
        $display("T2: obj1.val = %0d, obj2.val = %0d", t.obj1.val, t.obj2.val);
        if (t.obj1.val != 2) $stop;
        if (t.obj2.val != 5) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
