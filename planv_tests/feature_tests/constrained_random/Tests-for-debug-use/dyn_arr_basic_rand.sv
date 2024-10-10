class array;
    rand int dyn_arr[][];

    function new();
        dyn_arr = '{'{1, 2, 3}, '{4, 5, 6, 0, 10}, '{6, 7, 8, 9}};
        foreach(dyn_arr[i]) begin
            foreach(dyn_arr[i][j]) begin
                $display("i = %d, j = %d." , i, j);
            end
        end
        $display("--------------------------------------------");
        foreach(dyn_arr[i, j]) begin
            $display("i = %d, j = %d." , i, j);
        end
    endfunction

endclass

module dyn_arr_basic_rand;

    array cl;

  initial begin
    cl = new();

    $display("Dyn_arr Content:");
    $display("%p",cl.dyn_arr); 
    void'(cl.randomize());
    $display("%p",cl.dyn_arr); 

  end

endmodule