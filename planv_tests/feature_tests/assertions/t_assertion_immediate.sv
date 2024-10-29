// DESCRIPTION: PlanV Verilator Immediate Assertion Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

module t_assertion_immediate;
    int a = 5;
    int b = 10;

    initial begin
        // Immediate assertion should pass
        assert(a < b) else $fatal("Test failed: a is not less than b");

        // Immediate assertion should fail
        assert(b < a) else begin
            $display("Test passed: b is not less than a");
        end

        // End marker
        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
