// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_TDEFS_SVH__
`define __UVME_FIFO_TDEFS_SVH__

typedef uvma_wr_rd_agent_c #(uvma_wr_seq_item_c) write_agent_t;
typedef uvma_wr_rd_agent_c #(uvma_rd_seq_item_c) read_agent_t;

`endif  // __UVME_FIFO_TDEFS_SVH__
