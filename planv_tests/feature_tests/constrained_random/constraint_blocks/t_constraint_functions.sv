// DESCRIPTION: PlanV Verilator Functions in Constraints Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class C;
    rand bit [9:0] v;
    rand int length;

    // Function to count the number of ones in a packed array
    function int count_ones(bit [9:0] w);
        for (count_ones = 0; w != 0; w = w >> 1)
            count_ones += w & 1'b1;
    endfunction

    // Constraint using the count_ones function
    constraint count_ones_con {
        length == count_ones(v);
    }

    function new();
    endfunction
endclass

module t_constraint_functions;
    C obj = new();
    int i;

    initial begin
        for (i = 0; i < 100; i++) begin
            if (!obj.randomize()) $fatal("Randomization failed.");

            // Display the values
            $display("Randomization %0d:", i);
            $display("v = %b, length = %0d", obj.v, obj.length);

            // Validate that the constraint is indeed working
            if (obj.length != obj.count_ones(obj.v)) $fatal("Constraint violated: length != count_ones(v)");
        end

        $display("Functions in constraints test passed.");
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
