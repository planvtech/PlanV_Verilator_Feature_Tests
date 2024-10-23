// DESCRIPTION: PlanV Verilator ForEach Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class DynamicArrayConstraintTest;
    rand byte A[];
    rand int B[];

    constraint C1 {
        foreach (A[i]) A[i] inside {2, 4, 8, 16};
    }

    constraint C2 {
        foreach (A[j]) A[j] > 2 * j;
    }

    constraint C3 {
        A.size inside {[1:10]};
    }

    constraint C4 {
        foreach (B[k]) (k < B.size - 1) -> B[k + 1] > B[k];
    }

    function new();
    endfunction

    // Self-check function for array A
    function void check_array_A();
        foreach (A[i]) begin
            if (!(A[i] inside {2, 4, 8, 16})) $fatal("Constraint violated: A[%0d] = %0d", i, A[i]);
            if (!(A[i] > 2 * i)) $fatal("Constraint violated: A[%0d] = %0d", i, A[i]);
        end
    endfunction

    // Self-check function for array B
    function void check_array_B();
        foreach (B[i]) begin
            if (i < B.size - 1 && !(B[i + 1] > B[i])) $fatal("Constraint violated: B[%0d] = %0d, B[%0d] = %0d", i, B[i], i + 1, B[i + 1]);
        end
    endfunction
endclass

module t_constraint_foreach;
    DynamicArrayConstraintTest obj = new();
    int i;

    initial begin
        // Test foreach with array A
        if (!obj.randomize()) $fatal("Randomization failed.");
        obj.check_array_A();

        $display("Array A:");
        foreach (obj.A[i]) begin
            $display("A[%0d] = %0d", i, obj.A[i]);
        end

        // Test foreach with array B
        if (!obj.randomize()) $fatal("Randomization failed.");
        obj.check_array_B();

        $display("Array B:");
        foreach (obj.B[i]) begin
            $display("B[%0d] = %0d", i, obj.B[i]);
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
