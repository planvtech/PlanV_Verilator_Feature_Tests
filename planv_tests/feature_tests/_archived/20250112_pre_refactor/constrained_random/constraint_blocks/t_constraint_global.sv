// DESCRIPTION: PlanV Verilator Global Constraints Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
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
        if (!(obj.left.v <= obj.v)) begin
            $display("Constraint violated: left.v = %0d, v = %0d", obj.left.v, obj.v);
            $stop;
        end
        if (!(obj.right.v > obj.v)) begin 
            $display("Constraint violated: right.v = %0d, v = %0d", obj.right.v, obj.v);
            $stop;
        end

        $display("Global constraints test passed.");
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
