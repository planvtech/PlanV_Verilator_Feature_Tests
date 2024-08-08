class UniquenessConstraintTest;
    rand bit [7:0] value1;
    rand bit [7:0] value2;
    rand bit [7:0] value3;

    constraint unique_con {
        unique {value1, value2, value3};
    }

    function new();
    endfunction
endclass

module uniqueness_constraint_test;
    UniquenessConstraintTest uct;
    initial begin
        uct = new();
        repeat(10) begin
            if (!uct.randomize()) $error("Randomization failed");
            $display("value1: %0d, value2: %0d, value3: %0d", uct.value1, uct.value2, uct.value3);
        end
        $finish;
    end
endmodule