class Sub;
    rand bit [3:0] arr[2];
    constraint c { arr[0] == 5; }
endclass

class Top;
    rand Sub obj;
    function new();
        obj = new();
        obj.arr[0] = 10; // Initialize the first element to 10
    endfunction
endclass

module t_global_rand_t6;
    Top t = new();
    initial begin
        if (!t.randomize()) $stop;
        $display("T6: obj.arr[0] = %0d", t.obj.arr[0]);
        if (t.obj.arr[0] !== 5) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule