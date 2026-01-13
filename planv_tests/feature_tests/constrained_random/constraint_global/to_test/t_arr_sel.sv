// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

// Test global constraints with array selections (member[index].member)

class Inner;
    rand int val;
    constraint c_local { val inside {[10:20]}; }
    function new(); val = 0; endfunction
endclass

class Mid;
    rand Inner items[3];
    constraint c_mid {
        foreach (items[i]) items[i].val < 18;
    }
    function new();
        foreach (items[i]) items[i] = new();
    endfunction
endclass

class Top;
    rand Mid mids[2];
    rand int sum;

    // Global constraint with array selections: mids[0].items[1].val
    constraint c_global {
        mids[0].items[1].val < mids[1].items[2].val;
        sum == mids[0].items[0].val + mids[1].items[0].val;
        mids[0].items[1].val > 12;
    }

    function new();
        foreach (mids[i]) mids[i] = new();
        sum = 0;
    endfunction
endclass

module t_arr_sel;
    int success;
    Top t;

    initial begin
        t = new();

        // Test: randomize() with global constraints involving array selections
        success = t.randomize();
        if (success != 1) $stop;

        $display("mids[0].items[1].val=%0d, mids[1].items[2].val=%0d",
                 t.mids[0].items[1].val, t.mids[1].items[2].val);
        $display("sum=%0d, mids[0].items[0].val=%0d, mids[1].items[0].val=%0d",
                 t.sum, t.mids[0].items[0].val, t.mids[1].items[0].val);

        // Verify global constraints
        if (t.mids[0].items[1].val >= t.mids[1].items[2].val) $stop;
        if (t.sum != t.mids[0].items[0].val + t.mids[1].items[0].val) $stop;
        if (t.mids[0].items[1].val <= 12) $stop;

        // Verify local constraints
        foreach (t.mids[i]) begin
            foreach (t.mids[i].items[j]) begin
                if (t.mids[i].items[j].val < 10 || t.mids[i].items[j].val > 20) $stop;
                if (t.mids[i].items[j].val >= 18) $stop;
            end
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
