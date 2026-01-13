// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

module t_scope_std_randomize_class_bad1;
    class C;
        rand bit [7:0] a;
        bit [7:0] b;
        function new();
            a = 8'hFF;
            b = 8'hFF;
        endfunction
    endclass

    C c;
    function bit run();
        bit success;
        c = new();
        success = std::randomize(c.a, c.b); // ❌ ERROR: c.a is not in current scope\
        $display("a=%0h", c.a);
        $display("b=%0h", c.b);
        return success;
    endfunction

    initial begin
        bit ok;
        ok = run();
        $display("ok=%0d", ok);
        if (!ok) $stop;
    end
endmodule
