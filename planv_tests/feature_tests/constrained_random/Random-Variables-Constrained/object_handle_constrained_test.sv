class ObjectHandleTest;

    typedef struct {
        rand int a;
        rand int b;
    } UnpackedStruct;

    rand UnpackedStruct my_struct;
    rand ObjectHandleTest handle;
    
    function new();
        handle = new();
    endfunction

    // Constraint block
    constraint struct_constraint {
        my_struct.a inside {[0:100]};    // Constrain 'a' to be between 0 and 100
        my_struct.b > my_struct.a;       // Constrain 'b' to be greater than 'a'
    }
    
    constraint handle_constraint {
        handle.my_struct.a inside {[50:150]};
        handle.my_struct.b < 200;
    }
endclass

module object_handle_constrained_test;
    ObjectHandleTest obj_test;
    initial begin
        obj_test = new();
        repeat(10) begin
            if (!obj_test.randomize()) $error("Randomization failed");
            $display("a: %0d, b: %0d", obj_test.my_struct.a, obj_test.my_struct.b);
        end
        $finish;
    end
endmodule