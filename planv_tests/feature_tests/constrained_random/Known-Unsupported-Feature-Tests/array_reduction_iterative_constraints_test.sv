/*
    Known Unsupported Feature Tests due to the lack of support for "rand dyn_arr"
*/

class C;
    rand bit [7:0] A[];

    // Constraint: size of array A must be 5
    constraint c1 {
        A.size == 5;
    }

    // Constraint: sum of elements in array A must be less than 1000
    constraint c2 {
        A.sum() with (int'(item)) < 1000;
    }

    function new();
    endfunction
endclass

module array_reduction_iterative_constraints_test;

    C obj = new();
    
    initial begin
        int i;
        int sum = 0;
        if (!obj.randomize()) $fatal("Randomization failed.");

        $display("Array A:");
        
        foreach (obj.A[i]) begin
            $display("A[%0d] = %0d", i, obj.A[i]);
            sum += int'(obj.A[i]);
        end

        if (sum >= 1000) $fatal("Constraint violated: sum = %0d", sum);
        else $display("Sum of array A: %0d", sum);

        $finish;
    end
endmodule
