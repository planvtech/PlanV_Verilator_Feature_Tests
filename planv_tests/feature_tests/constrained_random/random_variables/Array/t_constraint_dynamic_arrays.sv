// DESCRIPTION: PlanV Verilator Constrained Randomization Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class ConstrainedDynamicArray;
    rand int dynamic_array[];             // Fully dynamic 1D array
    rand int fixed_dynamic_array_2d[3][]; // Fixed first dimension, dynamic second dimension
    rand int dynamic_fixed_array_2d[][2]; // Dynamic first dimension, fixed second dimension
    rand int dyn_arr_3d[][][];            // Fully dynamic 3D array
    rand bit [7:0] len;                   // Length for dynamic 1D array
    int count_dyn_arr_3d = 0;
    int count_fixed_dynamic_array_2d = 0;
    int count_dynamic_fixed_array_2d = 0;
    // Constraints for all arrays
    constraint size_constraint {
        dynamic_array.size == len;
        foreach (dynamic_array[i]) {
            dynamic_array[i] inside {[0:255]};
        }

        foreach (fixed_dynamic_array_2d[i]) {
            fixed_dynamic_array_2d[i].size == 2;
        }

        dynamic_fixed_array_2d.size() == 2;

        dyn_arr_3d.size() == 2;
        foreach (dyn_arr_3d[i]) {
            dyn_arr_3d[i].size() == 3;
            foreach (dyn_arr_3d[j]) {
                dyn_arr_3d[i][j].size() == 4;
            }
        }
    }

    // Constraint for sum of dynamic_array elements
    constraint sum_constraint {
        dynamic_array.sum() < 1000; // Sum of elements must be less than 1000
    }

    // Constraint for unique elements (nightmare for questasim)
    /*
    constraint unique_elements {
        foreach (dynamic_array[i]) {
            foreach (dynamic_array[j]) {
                if (i != j) {
                    dynamic_array[i] != dynamic_array[j]; // Ensure unique elements
                }
            }
        }
    }
    */
    function new();
        len = 10;  // Initial length of dynamic_array
    endfunction

    // Self-check function
    function void check();
        if (dynamic_array.size() == len) begin
            int sum;
            foreach (dynamic_array[i]) begin
                if (dynamic_array[i] inside {[0:255]}) begin
                    sum += dynamic_array[i];
                    $display("dynamic_array[%0d] = %0d is valid", i, dynamic_array[i]);
                end else begin
                    $display("Error: dynamic_array[%0d] = %0d is out of bounds", i, dynamic_array[i]);
                    $stop;
                end
            end
            if (sum > 1000) begin
                $display("Error: sum of dynamic_arrays = %0d is out of bounds", sum);
                $stop;
            end
        end else begin
            $display("Error: dynamic_array size = %0d does not match len = %0d", dynamic_array.size(), len);
            $stop;
        end

        foreach (fixed_dynamic_array_2d[i]) begin
            foreach (fixed_dynamic_array_2d[j]) begin
                $display("fixed_dynamic_array_2d[%0d][%0d] = %0d", i, j, fixed_dynamic_array_2d[i][j]);
                count_fixed_dynamic_array_2d += 1;
            end
        end

        foreach (dynamic_fixed_array_2d[i]) begin
            foreach (dynamic_fixed_array_2d[j]) begin
                $display("dynamic_fixed_array_2d[%0d][%0d] = %0d", i, j, dynamic_fixed_array_2d[i][j]);
                count_dynamic_fixed_array_2d += 1;
            end
        end

        foreach (dyn_arr_3d[i]) begin
            foreach (dyn_arr_3d[j]) begin
                foreach (dyn_arr_3d[k]) begin
                    $display("dyn_arr_3d[%0d][%0d][%0d] = %0d", i, j, k, dyn_arr_3d[i][j][k]);
                    count_dyn_arr_3d += 1;
                end
            end
        end

        if (count_fixed_dynamic_array_2d != 6) $stop;
        if (count_dynamic_fixed_array_2d != 4) $stop;
        if (count_dyn_arr_3d != 24) $stop;

    endfunction
endclass

module t_constraint_dynamic_arrays;
    ConstrainedDynamicArray array_test;

    initial begin
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
