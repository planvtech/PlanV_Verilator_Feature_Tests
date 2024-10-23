// DESCRIPTION: PlanV Verilator Basic Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class BasicConstraintTest;
    rand bit [7:0] value;

    constraint basic_con {
        value > 10 && value < 100;  // Constraint: value must be between 10 and 100
    }

    function new();
    endfunction

    // Self-check function
    function void check();
        if (!(value > 10 && value < 100)) begin
            $display("Error: value = %0d is out of bounds", value);
            $stop;  // Stop the test if the constraint is violated
        end
        $display("Constraint validated successfully: value = %0d", value);
    endfunction
endclass

module t_constraint_basic_test;
    BasicConstraintTest bct;

    initial begin
        bct = new();
        repeat(10) begin
            if (!bct.randomize()) $error("Randomization failed");

            // Self-check to validate constraints after randomization
            bct.check();

            // Displaying the values after randomization
            $display("value: %0d", bct.value);
        end
        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
