// Edge cases test for nested global constraints
// Tests specific scenarios that reveal the MemberSel fix

module test_edge_cases_nested;

    // Deep nesting test (4 levels)
    class Level4;
        rand int deepest;
        constraint c4 { deepest inside {[1:10]}; }
    endclass

    class Level3;
        rand Level4 l4;
        function new(); l4 = new(); endfunction
    endclass

    class Level2;
        rand Level3 l3;
        function new(); l3 = new(); endfunction
    endclass

    class Level1;
        rand Level2 l2;
        function new(); l2 = new(); endfunction
    endclass

    class DeepNestTest;
        rand Level1 obj_a;
        rand Level1 obj_b;

        function new();
            obj_a = new();
            obj_b = new();
        endfunction

        // 4-level deep nesting - ultimate test for the fix
        constraint deep_global {
            obj_a.l2.l3.l4.deepest > obj_b.l2.l3.l4.deepest;
        }

        function void test_deep();
            if (randomize()) begin
                $display("4-level nesting: obj_a=%0d, obj_b=%0d",
                        obj_a.l2.l3.l4.deepest, obj_b.l2.l3.l4.deepest);
                $display("SUCCESS: Deep nesting works!");
            end else begin
                $display("FAILED: 4-level nesting failed");
            end
        endfunction
    endclass

    // Array member test
    class ArrayMemberTest;
        rand int arr_data[3];
        constraint arr_c { foreach(arr_data[i]) arr_data[i] inside {[1:20]}; }
    endclass

    class ArrayContainer;
        rand ArrayMemberTest arr_obj;
        function new(); arr_obj = new(); endfunction
    endclass

    class ArrayGlobalTest;
        rand ArrayContainer cont1;
        rand ArrayContainer cont2;

        function new();
            cont1 = new();
            cont2 = new();
        endfunction

        // Test nested array access in global constraints
        constraint array_global {
            cont1.arr_obj.arr_data[0] < cont2.arr_obj.arr_data[0];
        }

        function void test_array();
            if (randomize()) begin
                $display("Array nesting: cont1.arr[0]=%0d, cont2.arr[0]=%0d",
                        cont1.arr_obj.arr_data[0], cont2.arr_obj.arr_data[0]);
                $display("SUCCESS: Array member nesting works!");
            end else begin
                $display("FAILED: Array member nesting failed");
            end
        endfunction
    endclass

    initial begin
        DeepNestTest deep_test;
        ArrayGlobalTest array_test;

        $display("=== Edge Cases for Nested Global Constraints ===");

        // Test 1: Very deep nesting
        $display("\n1. Testing 4-level deep nesting:");
        deep_test = new();
        deep_test.test_deep();

        // Test 2: Array member nesting
        $display("\n2. Testing array member nesting:");
        array_test = new();
        array_test.test_array();

        $display("\n=== Edge Cases Test Complete ===");
        $finish;
    end

endmodule