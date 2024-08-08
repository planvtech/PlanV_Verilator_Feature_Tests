class C;
    rand byte A[];
    rand int B[];

    // C1 constrains each element of the array A to be in the set [2, 4, 8, 16].
    constraint C1 {
        foreach (A[i]) A[i] inside {2, 4, 8, 16};
    }

    // C2 constrains each element of the array A to be greater than twice its index.
    constraint C2 {
        foreach (A[j]) A[j] > 2 * j;
    }

    // C3 constrains the size of the array A to be between 1 and 10.
    constraint C3 {
        A.size inside {[1:10]};
    }

    // C4 constrains each array value to be greater than the preceding one.
    constraint C4 {
        foreach (B[k]) (k < B.size - 1) -> B[k + 1] > B[k];
    }

    function new();
    endfunction
endclass

module foreach_iterative_constraints_test;

    C obj = new();
    int i;
    
    initial begin
        // Test foreach with array A
        if (!obj.randomize()) $fatal("Randomization failed.");

        $display("Array A:");
        foreach (obj.A[i]) begin
            $display("A[%0d] = %0d", i, obj.A[i]);
            if (!(obj.A[i] inside {2, 4, 8, 16})) $fatal("Constraint violated: A[%0d] = %0d", i, obj.A[i]);
            if (!(obj.A[i] > 2 * i)) $fatal("Constraint violated: A[%0d] = %0d", i, obj.A[i]);
        end

        // Test foreach with array B
        if (!obj.randomize()) $fatal("Randomization failed.");

        $display("Array B:");
        foreach (obj.B[i]) begin
            $display("B[%0d] = %0d", i, obj.B[i]);
            if (i < obj.B.size - 1 && !(obj.B[i + 1] > obj.B[i])) $fatal("Constraint violated: B[%0d] = %0d, B[%0d] = %0d", i, obj.B[i], i + 1, obj.B[i + 1]);
        end

        $finish;
    end
endmodule
