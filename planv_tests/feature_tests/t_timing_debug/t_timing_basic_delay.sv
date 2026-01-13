// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Contact: yilou.wang@planv.tech
//
// Phase 1: Basic timing delay test
// Test if simple #delay statements advance simulation time

module t_timing_basic_delay;
    int counter = 0;

    initial begin
        $display("[%0t] Starting test", $time);
        counter = 1;
        #100ns;
        $display("[%0t] After 100ns delay, counter=%0d", $time, counter);
        counter = 2;
        #200ns;
        $display("[%0t] After 200ns delay, counter=%0d", $time, counter);
        if ($time == 300000) begin  // 300ns in ps
            $display("*-* All Tests Passed *-*");
        end else begin
            $error("Time did not advance: $time=%0t", $time);
        end
        $finish;
    end
endmodule
