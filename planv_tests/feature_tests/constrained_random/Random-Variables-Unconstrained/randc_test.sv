class RandcTest;
    randc bit [3:0] cyclic_value;

    function new();
        cyclic_value = 4'b0001;
    endfunction
endclass

module randc_test;
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