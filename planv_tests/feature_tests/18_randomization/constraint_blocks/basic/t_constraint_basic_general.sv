// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: basic constraint block syntax and evaluation

`include "test_utils.svh"

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
            `DBG(("Error: value = %0d is out of bounds", value))
            $stop;  // Stop the test if the constraint is violated
        end
        `DBG(("Constraint validated successfully: value = %0d", value))
    endfunction
endclass

module t_constraint_basic_general;
    BasicConstraintTest bct;

    initial begin
        bct = new();
        repeat(10) begin
            if (!bct.randomize()) $error("Randomization failed");

            // Self-check to validate constraints after randomization
            bct.check();

            // Displaying the values after randomization
            `DBG(("value: %0d", bct.value))
        end
        `TEST_PASS  // End marker
    end
endmodule
