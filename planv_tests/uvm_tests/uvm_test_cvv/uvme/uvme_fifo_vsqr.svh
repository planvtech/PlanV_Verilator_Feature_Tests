// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_VSQR_SVH__
`define __UVME_FIFO_VSQR_SVH__


class uvme_fifo_vsqr_c extends uvm_sequencer#(
    .REQ(uvm_sequence_item),
    .RSP(uvm_sequence_item)
);

    // Objects
    uvme_fifo_cfg_c cfg;
    uvme_fifo_cntxt_c cntxt;

    // Sequencer Handles
    // uvma_wr_sqr_c write_sqr;
    // uvma_rd_sqr_c read_sqr;
    uvma_wr_rd_base_sqr_c #(uvma_wr_seq_item_c) write_sqr;
    uvma_wr_rd_base_sqr_c #(uvma_rd_seq_item_c) read_sqr;

    // Factory
    `uvm_component_utils_begin(uvme_fifo_vsqr_c)
        `uvm_field_object(cfg, UVM_ALL_ON)
        `uvm_field_object(cntxt, UVM_ALL_ON)
    `uvm_component_utils_end

    // Constructor

    extern function new(string name="uvme_fifo_vsqr_c", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);

endclass : uvme_fifo_vsqr_c


function uvme_fifo_vsqr_c::new(string name="uvme_fifo_vsqr_c", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


function void uvme_fifo_vsqr_c::build_phase(uvm_phase phase);

    super.build_phase(phase);
    
    `uvm_info("VSQR", "Entered build_phase", UVM_MEDIUM)

    void'(uvm_config_db#(uvme_fifo_cfg_c)::get(this, "", "cfg", cfg));
    if (cfg == null) begin
        `uvm_fatal("CFG", "cfg is null")
    end

    void'(uvm_config_db#(uvme_fifo_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("CNTXT", "cntxt is null")
    end

    `uvm_info("VSQR", "Exiting build_phase", UVM_MEDIUM)

endfunction : build_phase


`endif // __UVME_FIFO_VSQR_SVH__
