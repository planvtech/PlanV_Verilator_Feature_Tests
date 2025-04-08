// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef  __UVMA_WR_RD_PKG_SV__
`define  __UVMA_WR_RD_PKG_SV__

// Pre-processor macros
`include "uvm_macros.svh"
`include "uvma_wr_rd_macros.svh"


// Interfaces / Modules / Checkers
`include "uvma_wr_rd_if.sv"


package  uvma_wr_rd_pkg;

    import uvm_pkg::*;

    // Constants / Structs / Enums
    `include "uvma_wr_rd_constants.svh"
    `include "uvma_wr_rd_tdefs.svh"


    // Objects
    `include "uvma_wr_rd_cfg.svh"
    `include "uvma_wr_rd_cntxt.svh"


    // High-Level Transaction
    `include "uvma_wr_rd_seq_item.svh"


    // Components
    
    `include "uvma_wr_rd_drv.svh"
    `include "uvma_wr_rd_mon.svh"
    `include "uvma_wr_rd_sqr.svh"
    // `include "uvma_wr_rd_cov_model.svh"
    `include "uvma_wr_rd_agent.svh"


    // Sequences
    `include "uvma_wr_rd_base_seq.svh"
    `include "uvma_wr_rd_random_seq.svh"

    
endpackage : uvma_wr_rd_pkg

`endif // __UVMA_WR_RD_PKG_SV__
