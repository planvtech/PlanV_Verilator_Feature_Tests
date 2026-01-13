// DESCRIPTION: Verilator: Test this.randomize() in function
// Minimized test case to avoid crash

class Test;
    rand bit enabled;

    constraint cfg_con {
        enabled == 1;
    }

    // This function should randomize with constraints
    function int randomize_test();
        int result;
        result = this.randomize();
        return result;
    endfunction
endclass

module t_randomize_gen;
    initial begin
        Test t = new();
        int result;

        $display("=== Testing this.randomize() in function ===");

        result = t.randomize_test();

        $display("Randomization returned: %0d", result);
        $display("enabled = %0d (expected: 1)", t.enabled);

        if (result == 1 && t.enabled != 1) begin
            $display("*** BUG: randomize() returned success but constraints not applied! ***");
            $stop;
        end

        $display("*-* All Finished *-*");
        $finish;
    end
endmodule
