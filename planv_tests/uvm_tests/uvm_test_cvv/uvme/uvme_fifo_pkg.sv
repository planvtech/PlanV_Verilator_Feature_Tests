// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_PKG_SV__
`define __UVME_FIFO_PKG_SV__


// Preprocessor Macros
`include "uvm_macros.svh"
`include "uvma_wr_rd_macros.svh"
`include "uvme_fifo_macros.svh"

// Interfaces / Modules / Checkers


package uvme_fifo_pkg;

    import uvm_pkg::*;
    import uvma_wr_rd_pkg::*;

    // Constants, Structs, Enums
    `include "uvme_fifo_constants.svh"
    `include "uvme_fifo_tdefs.svh"

    // Objects
    `include "uvme_fifo_cfg.svh"
    `include "uvme_fifo_cntxt.svh"

    // Env Components
    
    `include "uvme_fifo_prdr.svh"
    `include "uvme_fifo_sb.svh"
    `include "uvme_fifo_vsqr.svh"

    // Virtual Sequence
    `include "uvme_fifo_base_vseq.svh"
    `include "uvme_fifo_random_vseq.svh"

    
    `include "uvme_fifo_env.svh"

endpackage : uvme_fifo_pkg


`endif // __UVME_FIFO_PKG_SV__
