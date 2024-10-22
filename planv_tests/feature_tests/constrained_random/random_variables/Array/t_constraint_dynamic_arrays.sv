// DESCRIPTION: PlanV Verilator Constrained Randomization Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class ConstrainedDynamicArray;
    // Various types of dynamic arrays
    rand int dynamic_array[];             // Fully dynamic 1D array
    rand int fixed_dynamic_array_2d[3][]; // Fixed first dimension, dynamic second dimension
    rand int dynamic_fixed_array_2d[][2]; // Dynamic first dimension, fixed second dimension
    rand int dyn_arr_3d[][][];            // Fully dynamic 3D array

    rand bit [7:0] len;  // Length for dynamic 1D array

    // Constraints for all arrays
    constraint size_constraint {
        dynamic_array.size == len;  // Array size constraint for dynamic_array based on len
        foreach (dynamic_array[i]) {
            dynamic_array[i] inside {[0:255]};  // Values constraint for dynamic_array (8-bit values)
        }
        fixed_dynamic_array_2d.size() == 3;  // Ensure fixed size for first dimension of fixed_dynamic_array_2d
        foreach (fixed_dynamic_array_2d[i]) {
            fixed_dynamic_array_2d[i].size() == 2;  // Dynamic size constraint for second dimension of fixed_dynamic_array_2d
        }
        dynamic_fixed_array_2d.size() == 2;  // Dynamic size for first dimension of dynamic_fixed_array_2d

        // Constraints for dyn_arr_3d
        dyn_arr_3d.size() == 2;  // Dynamic first dimension
        foreach (dyn_arr_3d[i]) {
            dyn_arr_3d[i].size() == 3;  // Dynamic second dimension
            foreach (dyn_arr_3d[i][j]) {
                dyn_arr_3d[i][j].size() == 4;  // Dynamic third dimension
            }
        }
    }

    // Constructor
    function new();
        len = 10;  // Initial length of dynamic_array
    endfunction

    // Self-check using if-else for validation
    function void check();
        if (dynamic_array.size() == len) begin
            foreach (dynamic_array[i]) begin
                if (dynamic_array[i] inside {[0:255]}) begin
                    $display("dynamic_array[%0d] = %0d is valid", i, dynamic_array[i]);
                end else begin
                    $display("Error: dynamic_array[%0d] = %0d is out of bounds", i, dynamic_array[i]);
                    $stop;
                end
            end
        end else begin
            $display("Error: dynamic_array size = %0d does not match len = %0d", dynamic_array.size(), len);
            $stop;
        end

        foreach (fixed_dynamic_array_2d[i]) begin
            foreach (fixed_dynamic_array_2d[i][j]) begin
                $display("fixed_dynamic_array_2d[%0d][%0d] = %0d", i, j, fixed_dynamic_array_2d[i][j]);
            end
        end

        foreach (dynamic_fixed_array_2d[i]) begin
            foreach (dynamic_fixed_array_2d[i][j]) begin
                $display("dynamic_fixed_array_2d[%0d][%0d] = %0d", i, j, dynamic_fixed_array_2d[i][j]);
            end
        end

        foreach (dyn_arr_3d[i]) begin
            foreach (dyn_arr_3d[i][j]) begin
                foreach (dyn_arr_3d[i][j][k]) begin
                    $display("dyn_arr_3d[%0d][%0d][%0d] = %0d", i, j, k, dyn_arr_3d[i][j][k]);
                end
            end
        end
    endfunction
endclass


module t_constraint_dynamic_arrays;
    ConstrainedDynamicArray array_test;

    initial begin
        // Test: Randomization for dynamic and mixed arrays, including 3D array
        $display("Test: Randomization for dynamic and mixed arrays:");
        array_test = new();
        repeat(2) begin
            if (!array_test.randomize()) begin
                $display("Randomization failed.");
                $stop;
            end
            array_test.check();
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
