// Test case for nested global randomization constraints
// This test verifies the fix for multi-level MemberSel in global constraints
// Author: Test case to verify commit c5671e9e0 improvements

module test_nested_global_constraints;

    // Inner-most class with randomizable variables
    class InnerData;
        rand int data_value;
        rand int inner_id;

        constraint basic_range {
            data_value inside {[1:100]};
            inner_id inside {[10:20]};
        }

        function void display(string prefix = "");
            $display("%s InnerData: data_value=%0d, inner_id=%0d",
                    prefix, data_value, inner_id);
        endfunction
    endclass

    // Middle class containing InnerData
    class MiddleContainer;
        rand InnerData inner_obj;
        rand int middle_value;

        function new();
            inner_obj = new();
        endfunction

        constraint middle_constraints {
            middle_value inside {[200:300]};
        }

        function void display(string prefix = "");
            $display("%s MiddleContainer: middle_value=%0d", prefix, middle_value);
            inner_obj.display(prefix + "  ");
        endfunction
    endclass

    // Outer class containing MiddleContainer
    class OuterWrapper;
        rand MiddleContainer middle_obj;
        rand int outer_value;

        function new();
            middle_obj = new();
        endfunction

        constraint outer_constraints {
            outer_value inside {[1000:2000]};
        }

        function void display(string prefix = "");
            $display("%s OuterWrapper: outer_value=%0d", prefix, outer_value);
            middle_obj.display(prefix + "  ");
        endfunction
    endclass

    // Top-level test class with global constraints
    class GlobalConstraintTest;
        rand OuterWrapper wrapper1;
        rand OuterWrapper wrapper2;
        rand int test_id;

        function new();
            wrapper1 = new();
            wrapper2 = new();
        endfunction

        // These are the CRITICAL global constraints that test the nested MemberSel fix
        // Before the fix: wrapper1.middle_obj.inner_obj.data_value would cause issues
        // After the fix: Should work correctly with proper path resolution
        constraint global_nested_constraints {
            // Single level access (should work in both versions)
            wrapper1.outer_value != wrapper2.outer_value;

            // Two-level nested access (this tests the first level of improvement)
            wrapper1.middle_obj.middle_value < wrapper2.middle_obj.middle_value;

            // Three-level nested access (this is the KEY test for the fix)
            // This should FAIL in the old version and WORK in the new version
            wrapper1.middle_obj.inner_obj.data_value +
            wrapper2.middle_obj.inner_obj.data_value < 150;

            // Complex nested relationships
            wrapper1.middle_obj.inner_obj.inner_id >
            wrapper2.middle_obj.inner_obj.inner_id;

            // Test ID constraints
            test_id inside {[1:10]};
        }

        function void display();
            $display("=== GlobalConstraintTest (ID=%0d) ===", test_id);
            $display("Wrapper1:");
            wrapper1.display("  ");
            $display("Wrapper2:");
            wrapper2.display("  ");
            $display("Global constraint check:");
            $display("  Sum of data_values: %0d (should be < 150)",
                    wrapper1.middle_obj.inner_obj.data_value +
                    wrapper2.middle_obj.inner_obj.data_value);
            $display("");
        endfunction

        function bit verify_constraints();
            bit result = 1;
            int sum_data = wrapper1.middle_obj.inner_obj.data_value +
                          wrapper2.middle_obj.inner_obj.data_value;

            if (sum_data >= 150) begin
                $display("ERROR: Global constraint violated - sum=%0d should be < 150", sum_data);
                result = 0;
            end

            if (wrapper1.middle_obj.inner_obj.inner_id <=
                wrapper2.middle_obj.inner_obj.inner_id) begin
                $display("ERROR: Inner ID constraint violated");
                result = 0;
            end

            if (wrapper1.middle_obj.middle_value >= wrapper2.middle_obj.middle_value) begin
                $display("ERROR: Middle value constraint violated");
                result = 0;
            end

            return result;
        endfunction
    endclass

    initial begin
        GlobalConstraintTest test_obj;
        int success_count = 0;
        int total_tests = 20;

        $display("Starting nested global constraint test...");
        $display("This test specifically validates the MemberSel chain fix in commit c5671e9e0");
        $display("");

        for (int i = 0; i < total_tests; i++) begin
            test_obj = new();

            // This randomize call will test the nested global constraints
            if (test_obj.randomize()) begin
                test_obj.display();
                if (test_obj.verify_constraints()) begin
                    success_count++;
                    $display("Test %0d: PASSED", i+1);
                end else begin
                    $display("Test %0d: FAILED - Constraint violation", i+1);
                end
            end else begin
                $display("Test %0d: FAILED - Randomization failed", i+1);
                $display("This likely indicates the old version where nested MemberSel doesn't work");
            end
            $display("----------------------------------------");
        end

        $display("Test Summary:");
        $display("Successful randomizations: %0d/%0d", success_count, total_tests);

        if (success_count == total_tests) begin
            $display("ALL TESTS PASSED - Nested global constraints working correctly");
        end else if (success_count == 0) begin
            $display("ALL TESTS FAILED - Likely using old version without nested MemberSel fix");
        end else begin
            $display("PARTIAL SUCCESS - May indicate implementation issues");
        end

        $finish;
    end

endmodule