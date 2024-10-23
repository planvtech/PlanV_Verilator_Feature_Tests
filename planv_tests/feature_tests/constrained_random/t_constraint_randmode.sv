// DESCRIPTION: PlanV Verilator Constraint Random Mode Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class SimpleSum;
    rand bit [7:0] x, y, z;
    constraint c { z == x + y; }
    constraint x_less_than_y { x < y; }

    function bit check_x_less_than_y();
        if (!(x < y)) begin
            $display("Error: x = %0d is not less than y = %0d", x, y);
            return 0;
        end
        return 1;
    endfunction

    function bit check_z_equals_x_plus_y();
        if (!(z == x + y)) begin
            $display("Error: z = %0d does not equal x + y (%0d + %0d)", z, x, y);
            return 0;
        end
        return 1;
    endfunction
endclass

module t_constraint_randmode;
    SimpleSum p = new();
    int success;

    initial begin
        success = p.randomize();
        if (success) begin
            $display("Initial randomization successful: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
            if (!p.check_z_equals_x_plus_y()) $stop;
            if (!p.check_x_less_than_y()) $stop;
        end else begin
            $display("Initial randomization failed.");
        end

        p.constraint_mode("x_less_than_y", 0);
        success = p.randomize();
        if (success) begin
            $display("Randomization without x_less_than_y constraint: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
            if (!p.check_z_equals_x_plus_y()) $stop;
        end else begin
            $display("Randomization failed without x_less_than_y constraint.");
        end

        p.constraint_mode("x_less_than_y", 1);
        success = p.randomize();
        if (success) begin
            $display("Randomization with x_less_than_y constraint: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
            if (!p.check_z_equals_x_plus_y()) $stop;
            if (!p.check_x_less_than_y()) $stop;
        end else begin
            $display("Randomization failed with x_less_than_y constraint.");
        end

        p.rand_mode("x", 0);
        success = p.randomize();
        if (success) begin
            $display("Randomization with x inactive: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
            if (!p.check_z_equals_x_plus_y()) $stop;
        end else begin
            $display("Randomization failed with x inactive.");
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
