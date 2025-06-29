class class_test;

    int a_cons;
    int a;
    int in;

    rand bit [07:0] addr;
    rand bit [31:0] data;
    rand bit [63:0] data_x_4;

    function int containt();
        int suz;
        suz = this.randomize() with { data  == addr * 8; 
                                                data_x_4 == data * 4;
                                            };
        $display("From new data = %0d", data);
        $display("From new data_x_4 = %0d", data_x_4);
        $display("From new addr = %0d", addr);
        return suz;
    endfunction

endclass


module t_scope_std_randomize_class;

    int success;
    class_test test;
    bit [8:0] a_r;

    initial begin

        test = new();
        // success = std::randomize(a_r, test.addr,test.data);
        $display("Valur a_rand = %0d, %0d, %0d",  test.data_x_4, test.addr,test.data);
        // success = test.containt();
        success = test.randomize() with { test.data  == test.addr * 8; 
                                                test.data_x_4 == test.data * 4;
                                            };
        $display("From new data = %0d", test.data);
        $display("From new data_x_4 = %0d", test.data_x_4);
        $display("From new addr = %0d", test.addr);
        // test.display();
        if (success != 1) $stop;

        $finish;
    end

endmodule : t_scope_std_randomize_class
