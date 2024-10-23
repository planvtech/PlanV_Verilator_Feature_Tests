// DESCRIPTION: PlanV Verilator Random Case Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

module t_rand_randcase;
    byte a, b;          
    bit [7:0] x;       
    int i;             
    int expected_value; 

    initial begin
        a = $urandom_range(0, 255);
        b = $urandom_range(0, 255);
        $display("Initial values: a = %0d, b = %0d", a, b);

        for (i = 0; i < 20; i++) begin
            randcase
                (a + b) : x = 1;
                (a - b) : x = 2;
                (a ^ ~b) : x = 3;
                12'h800 : x = 4;
            endcase

            // Determine expected value based on conditions
            if (a + b > 255) expected_value = 1;
            else if (a - b >= 0) expected_value = 2;
            else expected_value = 3;

            // Check if the selected value matches the expected value
            if (x == expected_value) begin
                $display("Iteration %0d: Selected x = %0d, which is as expected.", i + 1, x);
            end else begin
                $display("Iteration %0d: Selected x = %0d, which is NOT as expected (expected %0d).", i + 1, x, expected_value);
                $stop; // Stop the test if it doesn't match the expected value
            end
        end
        $write("*-* All Finished *-*\n"); // End marker
        $finish;
    end
endmodule
