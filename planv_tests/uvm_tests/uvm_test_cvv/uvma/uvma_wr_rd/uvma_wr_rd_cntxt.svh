// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMA_WR_RD_CNTXT_SVH__
`define __UVMA_WR_RD_CNTXT_SVH__

// To encapsulate all state_variables

class uvma_wr_rd_cntxt_c extends uvm_object;

    // Handle to agent interface
    virtual uvma_wr_if wr_vif;
    virtual uvma_rd_if rd_vif;

    // Data Monitoring

    // Events

    `uvm_object_utils_begin(uvma_wr_rd_cntxt_c)
    `uvm_object_utils_end

    // Constructor
    extern function new(string name="uvma_wr_rd_cntxt_c");

    extern function void reset();

endclass : uvma_wr_rd_cntxt_c 


function uvma_wr_rd_cntxt_c::new(string name="uvma_wr_rd_cntxt_c");
    
    super.new(name);

endfunction : new


function void uvma_wr_rd_cntxt_c::reset();
    
    // Reset all variables
    
endfunction : reset


`endif // __UVMA_WR_RD_CNTXT_SVH__
