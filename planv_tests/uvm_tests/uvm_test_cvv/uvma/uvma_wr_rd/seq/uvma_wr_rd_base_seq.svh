// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`ifndef __UVMA_WR_RD_BASE_SEQ_SVH__
`define __UVMA_WR_RD_BASE_SEQ_SVH__

class uvma_wr_rd_base_seq_c #(type SEQ_ITEM = uvm_sequence_item) extends uvm_sequence#(
    .REQ(SEQ_ITEM),
    .RSP(SEQ_ITEM)
);

    `uvm_object_utils(uvma_wr_rd_base_seq_c)
    `uvm_declare_p_sequencer(uvma_wr_rd_base_sqr_c #(SEQ_ITEM))

    extern function new(string name="uvma_wr_rd_base_seq");
    
endclass : uvma_wr_rd_base_seq_c


function uvma_wr_rd_base_seq_c::new(string name="uvma_wr_rd_base_seq");
    
    super.new(name);

endfunction : new


`endif // __UVMA_WR_RD_BASE_SEQ_SVH__
