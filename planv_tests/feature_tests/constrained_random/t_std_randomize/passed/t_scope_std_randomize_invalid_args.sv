// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

module t_scope_std_randomize_invalid_args;
    bit [3:0] a;

    function bit run();
        bit success;
        success = std::randomize(a + 1); // ❌ ERROR: argument is not a variable
        $display("a=%0h", a);
        return success;
    endfunction

    initial begin
        bit ok;
        ok = run();
        $display("ok=%0d", ok);
        if (!ok) $stop;
    end
endmodule
