// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class Inner;
    rand bit [3:0] val;
    function new();
        val = 2;
    endfunction
endclass

class Outer;
    rand Inner inner;
    rand bit [3:0] val;

    function new(int x);
        inner = new();
        this.val = x;
    endfunction

    constraint c_Outer {
        val < inner.val;
    }
    //constraint c_Inner {
    //    inner.val < 3;
    //}
    bit success;
    function void rand_inner();
        success = inner.randomize();
        if (!success) begin
            $display("Inner randomization failed");
        end
        $display("Inner value: %0d", inner.val);
    endfunction
endclass

module t_call_within_class;
    bit success, valid;
    Outer obj;

    initial begin
        obj = new(5);
        // success = obj.randomize();
        // valid = success && (obj.val < obj.inner.val) && (obj.inner.val < 5);
        obj.rand_inner();
        $display("Values: obj.val = %0d, obj.inner.val = %0d", obj.val, obj.inner.val);
        // if (!valid) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end 

endmodule
