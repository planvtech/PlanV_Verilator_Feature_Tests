class IfElseConstraintTest;
    rand int value;
    rand int flag;

    constraint conditional_con {
        if (flag) {
            value inside {1, 2, 3};
        } else {
            value inside {4, 5, 6};
        }
    }

    function new();
    endfunction
endclass

module if_else_constraint_test;
    IfElseConstraintTest cct;
    initial begin
        cct = new();
        repeat(10) begin
            if (!cct.randomize()) $error("Randomization failed");
            $display("flag: %0d, value: %0d", cct.flag, cct.value);
        end
        $finish;
    end
endmodule