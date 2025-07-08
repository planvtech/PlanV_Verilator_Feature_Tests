// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

module t_scope_std_randomize;
    bit [7:0] addr;
    bit [15:0] data;

    function bit run();
        int ready;
        bit success;
        bit [7:0] old_addr;
        bit [15:0] old_data;
        int old_ready;
        old_addr = addr;
        old_data = data;
        old_ready = ready;
        // $display("Before randomization: addr=%0h, data=%0h, ready=%0d", addr, data, ready);
        success = std::randomize(addr, ready);
        // $display("After: addr=%0h, data=%0h, ready=%0d", addr, data, ready);
        if (!success) return 0;
        if (addr == old_addr && data != old_data && ready == old_ready) begin
            // $display("Error: Randomization did not change any values.");
            return 0;
        end
        return 1;
    endfunction

    initial begin
        bit ok;
        ok = run();
        // $display("ok=%0d", ok);
        if (!ok) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
