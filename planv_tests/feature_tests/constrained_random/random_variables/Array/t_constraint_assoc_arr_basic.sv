module t_constraint_assoc_arr_basic;
    class assoc;
        rand bit [7:0] aa[string] = '{"XiaoMing":22, "MeiLi":32, "PanHong":31};
        constraint c {  // foreach (aa[ii]) aa[ii] < 10;  Foreach string situation, select always shows #x, unsupported issue
                    aa["XiaoMing"] inside {11, 12, 13};
                    aa["MeiLi"] == 66; 
                        }
        function display();
            foreach (aa[ii]) $display("The Value of aa[%s] is %d", ii, aa[ii]);
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