// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

interface fifo_w_if(input logic clk,reset);
    logic [7:0] data;
    logic en;
    logic full;
endinterface

interface fifo_r_if(input logic clk,reset);
    logic [7:0] data;
    logic en;
    logic empty;
endinterface