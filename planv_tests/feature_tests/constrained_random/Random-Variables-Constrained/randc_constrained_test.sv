class RandcTest;
    randc bit [3:0] cyclic_value;

    function new();
        cyclic_value = 4'b0001;
    endfunction

        // Constraint block
    constraint cyclic_constraint {
        cyclic_value inside {[4'b0010:4'b1010]};  // Constrain cyclic_value to be between 2 and 10
    }
    
endclass

module randc_constrained_test;
    RandcTest cyclic_test;
    initial begin
        cyclic_test = new();
        repeat(16) begin
            if (!cyclic_test.randomize()) $error("Randomization failed");
            $display("cyclic_value: %0b", cyclic_test.cyclic_value);
        end
        $finish;
    end
endmodule