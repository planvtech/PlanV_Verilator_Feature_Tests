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
                0 : x = 2;
                (a ^ ~b) : x = 3;
                12'h800 : x = 4;
            endcase

            // Check if the selected value matches the expected value
            if (x == 2) begin
                $display("Iteration %0d: Selected x = %0d, which is NOT as expected.", i + 1, x);
                $stop; // Stop the test if it doesn't match the expected value
            end
        end
        $write("*-* All Finished *-*\n"); // End marker
        $finish;
    end
endmodule
