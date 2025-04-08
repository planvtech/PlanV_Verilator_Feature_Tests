// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`ifndef __UVMA_WR_RD_RANDOM_SEQ_SVH__
`define __UVMA_WR_RD_RANDOM_SEQ_SVH__

class uvma_wr_random_seq_c extends uvma_wr_rd_base_seq_c #(uvma_wr_seq_item_c);

    `uvm_object_utils(uvma_wr_random_seq_c)

    extern function new(string name="uvma_wr_random_seq");

    extern virtual task body();

endclass : uvma_wr_random_seq_c


function uvma_wr_random_seq_c::new(string name="uvma_wr_random_seq");
    
    super.new(name);

endfunction : new


task uvma_wr_random_seq_c::body();

    uvma_wr_seq_item_c seq_item;
    seq_item = uvma_wr_seq_item_c::type_id::create("seq_item");
    start_item(seq_item);
    seq_item.randomize();
    finish_item(seq_item);

endtask : body



class uvma_rd_random_seq_c extends uvma_wr_rd_base_seq_c #(uvma_rd_seq_item_c);

    `uvm_object_utils(uvma_rd_random_seq_c)

    extern function new(string name="uvma_rd_random_seq");

    extern virtual task body();

endclass : uvma_rd_random_seq_c


function uvma_rd_random_seq_c::new(string name="uvma_rd_random_seq");
    
    super.new(name);

endfunction : new


task uvma_rd_random_seq_c::body();

    uvma_rd_seq_item_c seq_item;
    seq_item = uvma_rd_seq_item_c::type_id::create("seq_item");
    start_item(seq_item);
    seq_item.randomize();
    finish_item(seq_item);

endtask : body

`endif // __UVMA_WR_RD_RANDOM_SEQ_SVH__
