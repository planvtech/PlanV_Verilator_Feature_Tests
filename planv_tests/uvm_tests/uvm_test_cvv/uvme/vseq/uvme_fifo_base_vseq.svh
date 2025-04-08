// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`ifndef __UVME_FIFO_BASE_VSEQ_SVH__
`define __UVME_FIFO_BASE_VSEQ_SVH__


class uvme_fifo_base_vseq_c extends uvm_sequence#(
    .REQ(uvm_sequence_item),
    .RSP(uvm_sequence_item)
);

    // Environment Handles
    uvme_fifo_cfg_c cfg;
    uvme_fifo_cntxt_c cntxt;

    `uvm_object_utils(uvme_fifo_base_vseq_c)
    `uvm_declare_p_sequencer(uvme_fifo_vsqr_c)

    // Constructor
    extern function new(string name="uvme_fifo_base_vseq_c");
    extern virtual task pre_start();

endclass : uvme_fifo_base_vseq_c


function uvme_fifo_base_vseq_c::new(string name="uvme_fifo_base_vseq_c");
    
    super.new(name);

endfunction : new


task uvme_fifo_base_vseq_c::pre_start();
    
    cfg = p_sequencer.cfg;
    cntxt = p_sequencer.cntxt;

endtask : pre_start


`endif // __UVME_FIFO_BASE_VSEQ_SVH__
    