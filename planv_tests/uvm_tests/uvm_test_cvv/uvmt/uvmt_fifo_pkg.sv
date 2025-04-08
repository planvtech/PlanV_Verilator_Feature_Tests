// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMT_FIFO_PKG_SV__
`define __UVMT_FIFO_PKG_SV__

// Preprocessor Macros
`include "uvm_macros.svh"
// `include "uvmt_fifo_macros.svh"


`include "uvmt_fifo_tb_if.sv"

package uvmt_fifo_pkg;

    import uvm_pkg::*;
    import uvme_fifo_pkg::*;

    // Constants, Structs, Enums
    // `include "uvmt_fifo_constants.svh"
    // `include "uvmt_fifo_tdefs.svh"


    // Virtual Sequence Lib
    // TODO

    // Base Test case
    `include "uvmt_fifo_test_cfg.svh"
    `include "uvmt_fifo_test_randvars.svh"

    `include "uvmt_fifo_base_test.svh"
    `include "uvmt_fifo_test_case1.svh"

    // Test
    // `include "uvmt_fifo_test.svh"

endpackage : uvmt_fifo_pkg


`endif // __UVMT_FIFO_PKG_SV__
