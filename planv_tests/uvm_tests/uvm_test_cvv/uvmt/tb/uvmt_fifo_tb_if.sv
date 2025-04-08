// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMT_FIFO_TB_IF_SV__
`define __UVMT_FIFO_TB_IF_SV__

interface uvmt_fifo_clk_gen_if (output logic clk, output logic reset_n);

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    bit start_clk = 0;
    realtime clk_period = 10ns;
    realtime reset_deassert_duration = 7000ps;
    realtime reset_assert_duration = 7000ps;

    /**
     * Clock generation
     * If reset_n comes up de-asserted (1'b1), wait a bit, then assert, then de-assert
     * Otherwise, leave reset asserted, wait a bit, then de-assert
     */

    initial begin
        $display(">>> uvmt_fifo_clk_gen_if initial block entered at %0t", $time);
        clk = 0;
        reset_n = 0;
        wait(start_clk==1'b1);

        fork
            begin
                forever begin
                    #(clk_period / 2) clk = ~clk;
                end
            end
            begin
                if (reset_n == 1'b1) #(reset_assert_duration);
                reset_n = 1'b0;
                #(reset_deassert_duration);
                reset_n = 1'b1;
            end
        join_none

    end


    function static void set_clk_period(realtime period);
        clk_period = period * 1ps;
    endfunction


    function static void start_clk_gen();
        start_clk = 1;
        `uvm_info("uvmt_fifo_clk_gen_if", "Clock generation started", UVM_MEDIUM)
    endfunction

endinterface : uvmt_fifo_clk_gen_if

`endif // __UVMT_FIFO_TB_IF_SV__
