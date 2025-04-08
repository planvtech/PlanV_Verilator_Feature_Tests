// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMA_WR_RD_IF_SV__
`define __UVMA_WR_RD_IF_SV__


interface uvma_wr_if (input logic clk, reset_n);

    import uvm_pkg::*;

    // Signals
    logic [7:0] data;
    logic en;
    logic full;

    // Control fields

    // procedural blocks

endinterface : uvma_wr_if


interface uvma_rd_if (input logic clk, reset_n);

    import uvm_pkg::*;

    // Signals
    logic [7:0] data;
    logic en;
    logic empty;

    // Control fields

    // procedural blocks

endinterface : uvma_rd_if


`endif // __UVMA_WR_RD_IF_SV__
