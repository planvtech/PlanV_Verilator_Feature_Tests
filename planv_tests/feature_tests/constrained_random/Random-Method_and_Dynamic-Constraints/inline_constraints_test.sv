class SimpleSum;
    rand bit [7:0] x, y, z;
    constraint c {z == x + y;}
endclass

task InlineConstraintDemo(SimpleSum p);
    int success;
    success = p.randomize() with {x < y;};
    if (success) begin
        $display("Randomization successful: x = %0d, y = %0d, z = %0d", p.x, p.y, p.z);
    end else begin
        $display("Randomization failed.");
    end
endtask

module inline_constraints_test;
    SimpleSum p = new();

    initial begin
        InlineConstraintDemo(p);
        $finish;
    end
endmodule
