// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`ifndef __UVMA_WR_RD_SQR_SVH__
`define __UVMA_WR_RD_SQR_SVH__


class uvma_wr_rd_base_sqr_c#(type SEQ_ITEM = uvm_sequence_item) extends uvm_sequencer#(
    .REQ(SEQ_ITEM),
    .RSP(SEQ_ITEM)
);

    // objects
    uvma_wr_rd_cfg_c cfg;
    uvma_wr_rd_cntxt_c cntxt;

    // Factory
    `uvm_component_param_utils_begin(uvma_wr_rd_base_sqr_c#(SEQ_ITEM))
        `uvm_field_object(cfg, UVM_ALL_ON)
        `uvm_field_object(cntxt, UVM_ALL_ON)
    `uvm_component_utils_end

    extern function new(string name="uvma_wr_rd_base_sqr", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);

endclass : uvma_wr_rd_base_sqr_c


function uvma_wr_rd_base_sqr_c::new(string name="uvma_wr_rd_base_sqr", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


function void uvma_wr_rd_base_sqr_c::build_phase(uvm_phase phase);

    super.build_phase(phase);
    
    `uvm_info("SQR", "Entered build_phase", UVM_MEDIUM)

    void'(uvm_config_db#(uvma_wr_rd_cfg_c)::get(this, "", "cfg", cfg));
    if (cfg == null) begin
        `uvm_fatal("uvma_wr_rd_base_sqr_c", "cfg is null")
    end

    void'(uvm_config_db#(uvma_wr_rd_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("uvma_wr_rd_base_sqr_c", "cntxt is null")
    end

    `uvm_info("SQR", "Exiting build_phase", UVM_MEDIUM)

endfunction : build_phase


class uvma_wr_sqr_c extends uvma_wr_rd_base_sqr_c#(uvma_wr_seq_item_c);

    // Factory
    `uvm_component_utils_begin(uvma_wr_sqr_c)
    `uvm_component_utils_end

    extern function new(string name="uvma_wr_sqr_c", uvm_component parent=null);

endclass : uvma_wr_sqr_c

function uvma_wr_sqr_c::new(string name="uvma_wr_sqr_c", uvm_component parent=null);

    super.new(name, parent);

endfunction : new



class uvma_rd_sqr_c extends uvma_wr_rd_base_sqr_c#(uvma_rd_seq_item_c);

    // Factory
    `uvm_component_utils_begin(uvma_rd_sqr_c)
    `uvm_component_utils_end

    extern function new(string name="uvma_rd_sqr_c", uvm_component parent=null);

endclass : uvma_rd_sqr_c


function uvma_rd_sqr_c::new(string name="uvma_rd_sqr_c", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


`endif // __UVMA_WR_RD_SQR_SVH__
