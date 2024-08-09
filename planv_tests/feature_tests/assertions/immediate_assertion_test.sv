module immediate_assertion_test;
    int a = 5;
    int b = 10;

    initial begin
        // Immediate assertion should pass
        assert(a < b) else $fatal("Test failed: a is not less than b");

        // Immediate assertion should fail
        assert(b < a) else $display("Test passed: b is not less than a");

        $finish;
    end
endmodule
