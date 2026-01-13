class Sub;
    rand bit [3:0] val;
    constraint c { val inside {[1:3]}; }
endclass

class Top;
    rand Sub objs[2];
    function new();
        objs[0] = new();
        objs[1] = new();
    endfunction
endclass

module t_global_rand_t5;
    Top t = new();
    initial begin
        if (!t.randomize()) $stop;
        foreach (t.objs[i]) begin
            $display("T5: objs[%0d].val = %0d", i, t.objs[i].val);
            if (t.objs[i].val < 1 || t.objs[i].val > 3) $stop;
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule