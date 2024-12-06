module t_constraint_assoc_arr_basic;
    class assoc;
        rand bit [7:0] aa[int] = '{0:22, 16:32, 12:3};
        constraint c { foreach(aa[ii]) aa[ii] < 10; }

        function display();
            foreach (aa[ii]) $display("Value is %d", aa[ii]);
        endfunction
    endclass

    assoc h;
    int i;
    initial begin
        h = new;
        i = h.randomize();
        $display(i);
        h.display();
    end

endmodule