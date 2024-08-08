class SimpleSum;
    rand bit [7:0] x, y, z;
    constraint c { z == x + y; }
    constraint x_less_than_y { x < y; }
endclass

module constraint_rand_mode_test;
    SimpleSum p = new();
    int success;

    initial begin
        // Initial constraints: both x_less_than_y and c are active
        success = p.randomize();
        if (success) begin
            $display("Initial randomization successful: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
        end else begin
            $display("Initial randomization failed.");
        end

        // Deactivate x_less_than_y constraint
        p.constraint_mode("x_less_than_y", 0);
        success = p.randomize();
        if (success) begin
            $display("Randomization without x_less_than_y constraint: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
        end else begin
            $display("Randomization failed without x_less_than_y constraint.");
        end

        // Reactivate x_less_than_y constraint
        p.constraint_mode("x_less_than_y", 1);
        success = p.randomize();
        if (success) begin
            $display("Randomization with x_less_than_y constraint: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
        end else begin
            $display("Randomization failed with x_less_than_y constraint.");
        end

        // Deactivate x variable
        p.rand_mode("x", 0);
        success = p.randomize();
        if (success) begin
            $display("Randomization with x inactive: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
        end else begin
            $display("Randomization failed with x inactive.");
        end

        $finish;
    end
endmodule
