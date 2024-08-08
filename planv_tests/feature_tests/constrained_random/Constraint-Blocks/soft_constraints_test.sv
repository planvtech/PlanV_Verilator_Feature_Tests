class Packet;
    rand bit mode;
    rand int length;

    constraint deflt { 
        soft length inside {32, 1024}; 
        soft mode -> length == 1024;
    }
endclass

module soft_constraints_test;
    Packet p = new();
    int i;

    initial begin
        for (i = 0; i < 100; i++) begin
            // Test case where length is overridden
            if (!p.randomize() with { length == 1512; }) $fatal("Randomization failed.");

            // Display the values
            $display("Randomization %0d: length = %0d, mode = %0b", i, p.length, p.mode);
            if (p.length != 1512) $fatal("Soft constraint was not overridden properly.");

            // Test case where both length and mode are overridden
            if (!p.randomize() with { length == 1512; mode == 1; }) $fatal("Randomization failed.");

            // Display the values
            $display("Randomization %0d: length = %0d, mode = %0b", i, p.length, p.mode);
            if (p.length != 1512 || p.mode != 1) $fatal("Soft constraint was not overridden properly.");
        end

        $display("Soft constraints test passed.");
        $finish;
    end
endmodule