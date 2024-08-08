class BasicConstraintTest;
    rand bit [7:0] value;

    constraint basic_con {
        value > 10 && value < 100;
    }

    function new();
    endfunction
endclass

module basic_constraint_test;
    BasicConstraintTest bct;
    initial begin
        bct = new();
        repeat(10) begin
            if (!bct.randomize()) $error("Randomization failed");
            $display("value: %0d", bct.value);
        end
        $finish;
    end
endmodule