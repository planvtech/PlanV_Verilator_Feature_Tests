class array;
    int dyn_arr[][];
    int unpacked_arr [3:1][9:8];
    rand int queue[$][$];

    function new();
        queue = '{'{1, 2, 3}, '{4, 5, 6, 0, 10}, '{6, 7, 8, 9}};
        $display("Queue:");
        foreach(queue[i]) begin
            foreach(queue[i][j]) begin
                $display("i = %d, j = %d." , i, j);
            end
        end
        $display("--------------------------------------------");
        foreach(queue[i, j]) begin
            $display("i = %d, j = %d." , i, j);
        end

        $display("Dyn Arr:");
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

        $display("Unpacked Arr:");
        foreach(unpacked_arr[i]) begin
            foreach(unpacked_arr[i][j]) begin
                $display("i = %d, j = %d." , i, j);
            end
        end
        $display("--------------------------------------------");
        foreach(unpacked_arr[i, j]) begin
            $display("i = %d, j = %d." , i, j);
        end
    endfunction

endclass

module queue_basic_rand;

    array cl;

  initial begin
    cl = new();

    $display("Queue Content:");
    $display("%p",cl.queue); 
    void'(cl.randomize());
    $display("%p",cl.queue); 

  end

endmodule