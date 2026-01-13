// Simplified test case for nested global constraints
// This test focuses on the specific scenarios that were fixed

module test_simple_nested_constraints;

    // Simple inner class
    class DataClass;
        rand int value;
        constraint basic { value inside {[1:50]}; }
    endclass

    // Container class
    class Container;
        rand DataClass data;
        function new(); data = new(); endfunction
    endclass

    // Test class with global constraints
    class SimpleTest;
        rand Container obj1;
        rand Container obj2;

        function new();
            obj1 = new();
            obj2 = new();
        endfunction

        // This is the KEY constraint that tests the nested MemberSel fix
        constraint global_nested {
            // Two-level nesting: obj1.data.value
            // This should FAIL on old version, WORK on new version
            obj1.data.value + obj2.data.value < 80;
            obj1.data.value != obj2.data.value;
        }

        function void display();
            $display("obj1.data.value = %0d", obj1.data.value);
            $display("obj2.data.value = %0d", obj2.data.value);
            $display("Sum = %0d (should be < 80)", obj1.data.value + obj2.data.value);
        endfunction
    endclass

    initial begin
        SimpleTest test;
        $display("=== Simple Nested Constraint Test ===");
        $display("Testing: obj1.data.value + obj2.data.value < 80");

        test = new();
        if (test.randomize()) begin
            $display("SUCCESS: Randomization worked!");
            test.display();
        end else begin
            $display("FAILED: Randomization failed (likely old version issue)");
        end
        $finish;
    end

endmodule