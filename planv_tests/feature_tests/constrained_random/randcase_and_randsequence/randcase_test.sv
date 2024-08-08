module randcase_test;
    byte a, b;
    bit [7:0] x;
    int i;

    initial begin
        // Set random values for a and b
        a = $urandom_range(0, 255);
        b = $urandom_range(0, 255);
        $display("Initial values: a = %0d, b = %0d", a, b);

        // Repeat the randcase selection multiple times to observe the distribution
        for (i = 0; i < 20; i++) begin
            randcase
                (a + b) : x = 1;
                (a - b) : x = 2;
                (a ^ ~b) : x = 3;
                12'h800 : x = 4;
            endcase
            $display("Iteration %0d: Selected x = %0d", i+1, x);
        end
        $finish;
    end
endmodule
