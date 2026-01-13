// DESCRIPTION: PlanV Verilator Soft Constraint Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class DisableSoftConstraintTest;
    rand bit [7:0] value;

    constraint soft_con {
        soft value == 10;
    }

    function new();
    endfunction
endclass

class Packet;
    rand bit mode;
    rand int length;

    constraint deflt { 
        soft length inside {32, 1024}; 
        soft mode -> length == 1024;
    }
endclass

module t_constraint_soft;
    DisableSoftConstraintTest dsct;
    Packet p = new();
    int i;

    initial begin
        dsct = new();
        repeat(10) begin
            if (!dsct.randomize()) $error("Randomization failed");
            $display("DisableSoftConstraintTest value: %0d", dsct.value);
        end

        for (i = 0; i < 100; i++) begin
            if (!p.randomize() with { length == 1512; }) $fatal("Randomization failed.");

            $display("Randomization %0d: length = %0d, mode = %0b", i, p.length, p.mode);
            if (p.length != 1512) $fatal("Soft constraint was not overridden properly.");

            if (!p.randomize() with { length == 1512; mode == 1; }) $fatal("Randomization failed.");

            $display("Randomization %0d: length = %0d, mode = %0b", i, p.length, p.mode);
            if (p.length != 1512 || p.mode != 1) $fatal("Soft constraint was not overridden properly.");
        end

        $display("Soft constraints test passed.");
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
