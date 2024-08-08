class DisableSoftConstraintTest;
    rand bit [7:0] value;

    constraint soft_con {
        soft value == 10;
    }

    function new();
    endfunction
endclass

module disable_soft_constraint_test;
    DisableSoftConstraintTest dsct;
    initial begin
        dsct = new();
        repeat(10) begin
            if (!dsct.randomize()) $error("Randomization failed");
            $display("value: %0d", dsct.value);
        end
        $finish;
    end
endmodule