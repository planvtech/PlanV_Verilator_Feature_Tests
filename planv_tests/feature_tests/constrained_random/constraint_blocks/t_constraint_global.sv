// DESCRIPTION: PlanV Verilator Global Constraints Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

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

module t_constraint_global;
    B obj = new();

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
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
