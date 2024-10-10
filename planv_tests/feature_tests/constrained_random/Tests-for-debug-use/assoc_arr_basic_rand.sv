class array;

    rand int assoc_arr[string][string];

    function new();
        assoc_arr["John"]["Math"] = 85;
        assoc_arr["John"]["Science"] = 90;
        assoc_arr["Alice"]["Math"] = 75;
        assoc_arr["Alice"]["Science"] = 80;
    endfunction

    task display_assoc_array();
        $display(assoc_arr);
        $display(assoc_arr["John"]["Science"]);
        $display(assoc_arr["Alice"]["Science"]);
        $display(assoc_arr["Alice"]);
    endtask
endclass

module assoc_arr_basic_rand;

    array cl;

  initial begin
    cl = new();

    $display("Associative Array Content:");
    $display("%p",cl.assoc_arr); 
    //cl.display_assoc_array();
    void'(cl.randomize());
    $display("%p",cl.assoc_arr); 
    //cl.display_assoc_array();

  end

endmodule
