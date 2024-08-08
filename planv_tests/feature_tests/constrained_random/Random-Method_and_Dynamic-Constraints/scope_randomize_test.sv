module scope_randomize_test;
    // Define variables in module scope
    bit [15:0] addr;
    bit [31:0] data;
    bit rd_wr;
    int success;

    // Function to generate stimulus
    function bit gen_stim();
        success = std::randomize(addr, data, rd_wr); // Call std::randomize
        return rd_wr;
    endfunction

    // Task to demonstrate inline constraints with std::randomize
    task stimulus(int length);
        int a, b, c;
        success = std::randomize(a, b, c) with { a < b; a + b < length; }; // Constrain a, b, and c
        $display("Randomized values with constraints (a < b, a + b < length): a = %0d, b = %0d, c = %0d, length = %0d", a, b, c, length);
        
        success = std::randomize(a, b) with { b - a > length; }; // Constrain a and b
        $display("Randomized values with constraints (b - a > length): a = %0d, b = %0d, length = %0d", a, b, length);
    endtask

    initial begin
        // Call the gen_stim function
        rd_wr = gen_stim();
        if (success) begin
            $display("Scope randomize successful: addr = %0d, data = %0d, rd_wr = %0b", addr, data, rd_wr);
        end else begin
            $display("Scope randomize failed.");
        end

        // Call the stimulus task with different lengths
        stimulus(50);
        stimulus(100);

        $finish;
    end
endmodule
