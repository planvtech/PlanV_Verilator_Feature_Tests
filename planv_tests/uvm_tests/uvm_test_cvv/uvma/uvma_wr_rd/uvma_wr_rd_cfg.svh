// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`ifndef __UVMA_WR_RD_CFG_SVH__
`define __UVMA_WR_RD_CFG_SVH__

// To encapsulate all parameters for creating, connecting and running

class uvma_wr_rd_cfg_c extends uvm_object;
    
    // Common Options
    rand bit enabled;
    rand uvm_active_passive_enum is_active; // Decide whether the drv.ap is active for the input sequence
    // rand uvm_sequencer_arb_mode sqr_arb_mode;
    rand wr_or_rd_t wr_or_rd; // Decide which type of sequence_item
    rand bit cov_model_enabled;
    rand bit trn_log_enabled;

    // Implementation Options

    // rand bit enable_drv;

    `uvm_object_utils_begin(uvma_wr_rd_cfg_c)
        `uvm_field_int(enabled, UVM_ALL_ON)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
        // `uvm_field_enum(uvm_sequencer_arb_mode, sqr_arb_mode, UVM_ALL_ON)
        `uvm_field_enum(wr_or_rd_t, wr_or_rd, UVM_ALL_ON)
        `uvm_field_int(cov_model_enabled, UVM_ALL_ON)
        `uvm_field_int(trn_log_enabled, UVM_ALL_ON)
    `uvm_object_utils_end

    `ifndef VERILATOR
    constraint default_con {
        soft enabled == 0;
        soft is_active == UVM_PASSIVE;
        // sqr_arb_mode == UVM_SEQ_ARB_FIFO;
        soft cov_model_enabled == 0;
        soft trn_log_enabled == 0;
    }
    `endif

    extern function new(string name="uvma_wr_rd_cfg_c");

endclass : uvma_wr_rd_cfg_c


function uvma_wr_rd_cfg_c::new(string name="uvma_wr_rd_cfg_c");
    
    super.new(name);

endfunction : new


`endif // __UVMA_WR_RD_CFG_SVH__
