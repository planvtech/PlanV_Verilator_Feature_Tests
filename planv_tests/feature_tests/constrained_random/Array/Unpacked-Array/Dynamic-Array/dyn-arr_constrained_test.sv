class DynamicArrayTest;
    rand bit [7:0] len;
    rand int data[];
    
    constraint size_constraint {
        data.size == len;
        foreach (data[i]) {
            data[i] inside {[0:255]};  // Constraint on the values in the array (e.g., 8-bit values)
        }
    }

    function new();
        len = 10;
    endfunction
endclass

module dynamic_array_constrained_test;
    DynamicArrayTest array_test;
    initial begin
        array_test = new();
        repeat(10) begin
            if (!array_test.randomize()) $error("Randomization failed");
            $display("len: %0d, data: %p", array_test.len, array_test.data);
        end
        $finish;
    end
endmodule