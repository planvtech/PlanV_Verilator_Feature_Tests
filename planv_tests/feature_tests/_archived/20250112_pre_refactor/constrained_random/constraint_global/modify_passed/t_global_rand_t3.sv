// Comprehensive test for nested global constraints
// Tests: 4-layer nesting, multiple instances, mixed constraints

// Level 4: Deepest nested class
class Level4;
    rand int deep_value;
    constraint c4 { deep_value inside {[1:10]}; }

    function new();
        deep_value = 0;
    endfunction
endclass

// Level 3: Contains Level4
class Level3;
    rand Level4 l4;
    rand int value3;
    constraint c3 { value3 inside {[10:20]}; }

    function new();
        l4 = new();
        value3 = 0;
    endfunction
endclass

// Level 2: Contains Level3 and has multiple instances scenario
class Level2;
    rand Level3 l3;
    rand int value2;
    constraint c2 { value2 > 20; }

    function new();
        l3 = new();
        value2 = 0;
    endfunction
endclass

// Level 1: Contains Level2
class Level1;
    rand Level2 l2;
    rand int value1;

    function new();
        l2 = new();
        value1 = 0;
    endfunction
endclass

// Top class with comprehensive global constraints
class TopLevel;
    rand Level1 obj_a;
    rand Level1 obj_b;
    rand Level1 obj_c;  // Third instance to test multiple same-type objects
    rand int top_value;

    // Global constraints testing 4-layer nesting and multiple instances
    constraint global_constraints {
        // Test 1: 4-layer nesting access (obj_a.l2.l3.l4.deep_value)
        obj_a.l2.l3.l4.deep_value < 5;
        obj_b.l2.l3.l4.deep_value > 5;
        obj_c.l2.l3.l4.deep_value == 5;

        // Test 2: Multiple instances of same class type
        obj_a.l2.value2 < obj_b.l2.value2;
        obj_b.l2.value2 < obj_c.l2.value2;

        // Test 3: Mixed depth access in single constraint
        obj_a.l2.l3.value3 + obj_b.l2.l3.value3 < 35;

        // Test 4: Constraint on top-level variable
        top_value == obj_a.l2.l3.l4.deep_value + obj_b.l2.l3.l4.deep_value + obj_c.l2.l3.l4.deep_value;

        // Test 5: Cross-object relationships at different nesting levels
        obj_a.value1 < obj_b.l2.value2;
        obj_b.value1 < obj_c.l2.l3.value3;
    }

    function new();
        obj_a = new();
        obj_b = new();
        obj_c = new();
        top_value = 0;
    endfunction
endclass

module t_global_rand_t3;
    int success;
    TopLevel top;

    initial begin
        top = new();
        success = top.randomize();

        // Check randomization succeeded
        if (success != 1) begin
            $display("ERROR: Randomization failed");
            $stop;
        end

        // Display results
        $display("T3: Randomization successful");
        $display("T3: obj_a.l2.l3.l4.deep_value = %0d (should be < 5)",
                 top.obj_a.l2.l3.l4.deep_value);
        $display("T3: obj_b.l2.l3.l4.deep_value = %0d (should be > 5)",
                 top.obj_b.l2.l3.l4.deep_value);
        $display("T3: obj_c.l2.l3.l4.deep_value = %0d (should be == 5)",
                 top.obj_c.l2.l3.l4.deep_value);
        $display("T3: top_value = %0d (should be sum of deep_values)", top.top_value);

        // Verify constraints
        // Test 1: 4-layer nesting constraints
        if (top.obj_a.l2.l3.l4.deep_value >= 5) begin
            $display("ERROR: obj_a.l2.l3.l4.deep_value constraint violated");
            $stop;
        end
        if (top.obj_b.l2.l3.l4.deep_value <= 5) begin
            $display("ERROR: obj_b.l2.l3.l4.deep_value constraint violated");
            $stop;
        end
        if (top.obj_c.l2.l3.l4.deep_value != 5) begin
            $display("ERROR: obj_c.l2.l3.l4.deep_value constraint violated");
            $stop;
        end

        // Test 2: Multiple instances ordering
        if (top.obj_a.l2.value2 >= top.obj_b.l2.value2) begin
            $display("ERROR: obj_a.l2.value2 < obj_b.l2.value2 violated");
            $stop;
        end
        if (top.obj_b.l2.value2 >= top.obj_c.l2.value2) begin
            $display("ERROR: obj_b.l2.value2 < obj_c.l2.value2 violated");
            $stop;
        end

        // Test 3: Sum constraint
        if (top.obj_a.l2.l3.value3 + top.obj_b.l2.l3.value3 >= 35) begin
            $display("ERROR: Sum of value3 constraint violated");
            $stop;
        end

        // Test 4: Top value calculation
        if (top.top_value != (top.obj_a.l2.l3.l4.deep_value +
                              top.obj_b.l2.l3.l4.deep_value +
                              top.obj_c.l2.l3.l4.deep_value)) begin
            $display("ERROR: top_value calculation incorrect");
            $stop;
        end

        // Test 5: Cross-level constraints
        if (top.obj_a.value1 >= top.obj_b.l2.value2) begin
            $display("ERROR: Cross-level constraint 1 violated");
            $stop;
        end
        if (top.obj_b.value1 >= top.obj_c.l2.l3.value3) begin
            $display("ERROR: Cross-level constraint 2 violated");
            $stop;
        end

        // Test 6: Internal constraints still work
        if (top.obj_a.l2.l3.l4.deep_value < 1 || top.obj_a.l2.l3.l4.deep_value > 10) begin
            $display("ERROR: Internal constraint c4 violated for obj_a");
            $stop;
        end
        if (top.obj_a.l2.l3.value3 < 10 || top.obj_a.l2.l3.value3 > 20) begin
            $display("ERROR: Internal constraint c3 violated for obj_a");
            $stop;
        end

        $display("T3: All constraints verified successfully");
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
