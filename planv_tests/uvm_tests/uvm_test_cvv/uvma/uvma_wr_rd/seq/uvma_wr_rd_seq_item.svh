// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMA_WR_RD_SEQ_ITEM_SVH__
`define __UVMA_WR_RD_SEQ_ITEM_SVH__


class uvma_wr_seq_item_c extends uvm_sequence_item;

    // Signals
    rand logic[7:0] w_data;
    rand logic w_en;
    rand logic w_full;

    // Variables
    rand int delay;
    rand logic flag;


    `uvm_object_utils_begin(uvma_wr_seq_item_c)
        `uvm_field_int(w_data, UVM_ALL_ON)
        `uvm_field_int(w_en, UVM_ALL_ON)
        `uvm_field_int(w_full, UVM_ALL_ON)
        `uvm_field_int(delay, UVM_ALL_ON)
        `uvm_field_int(flag, UVM_ALL_ON)
    `uvm_object_utils_end

    // Constraints
    constraint default_con {
        soft w_en == 1;
        soft w_full == 0;
        soft delay == 0;
    }

    // Constructor
    extern function new(string name="uvma_wr_seq_item");

endclass : uvma_wr_seq_item_c


function uvma_wr_seq_item_c::new(string name="uvma_wr_seq_item");
    
    super.new(name);

endfunction : new



class uvma_rd_seq_item_c extends uvm_sequence_item;

    // Signals
    rand bit r_en;
    rand bit[7:0] r_data;
    rand bit r_empty;

    // Variables
    rand int delay;

    // Factory
    `uvm_object_utils_begin(uvma_rd_seq_item_c)
        `uvm_field_int(r_en, UVM_ALL_ON)
        `uvm_field_int(r_data, UVM_ALL_ON)
        `uvm_field_int(r_empty, UVM_ALL_ON)
        `uvm_field_int(delay, UVM_ALL_ON)
    `uvm_object_utils_end

    // Constraints
    constraint default_con {
        soft r_en == 1;
        soft r_empty == 0;
        soft delay == 0;
    }

    // Constructor
    extern function new(string name="uvma_rd_seq_item_c");

endclass : uvma_rd_seq_item_c


function uvma_rd_seq_item_c::new(string name="uvma_rd_seq_item_c");
    
    super.new(name);

endfunction : new


`endif // __UVMA_WR_RD_SEQ_ITEM_SVH__
