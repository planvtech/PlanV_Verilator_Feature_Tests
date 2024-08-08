class A;
    rand bit [7:0] v;

    function new();
    endfunction
endclass

class B extends A;
    rand A left;
    rand A right;

    constraint heapcond {
        left.v <= v;
        right.v > v;
    }

    function new();
        left = new();
        right = new();
    endfunction
endclass

module global_constraints_test;

    B obj = new();
    int i;

    initial begin
        if (!obj.randomize()) $fatal("Randomization failed.");

        // Display the values of the heap node and its children
        $display("Heap node value: %0d", obj.v);
        $display("Left child value: %0d", obj.left.v);
        $display("Right child value: %0d", obj.right.v);

        // Validate constraints
        assert(obj.left.v <= obj.v) else $fatal("Constraint violated: left.v = %0d, v = %0d", obj.left.v, obj.v);
        assert(obj.right.v > obj.v) else $fatal("Constraint violated: right.v = %0d, v = %0d", obj.right.v, obj.v);

        $display("Global constraints test passed.");
        $finish;
    end
endmodule
