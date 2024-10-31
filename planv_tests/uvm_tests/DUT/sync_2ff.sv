// DESCRIPTION: PlanV Async Fifo DUT
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

// `timescale 1ns/1ps
module sync_2ff #(
    parameter ADDR_SIZE = 4
) (
    o_ptr,
    i_ptr,
    clk,
    rst
);
    input  [ADDR_SIZE : 0] i_ptr;
    output logic [ADDR_SIZE : 0] o_ptr;
    input clk;
    input rst;

    logic [ADDR_SIZE : 0] ptr_temp;

    always @(posedge clk or negedge rst) begin
        if(rst != 1) begin
            ptr_temp <= 0;
            o_ptr <= 0;
        end else begin
            ptr_temp <= i_ptr;
            o_ptr <= ptr_temp;
        end
    end
endmodule