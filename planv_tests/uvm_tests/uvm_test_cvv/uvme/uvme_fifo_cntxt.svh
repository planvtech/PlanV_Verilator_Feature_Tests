// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_CNTXT_SVH__
`define __UVME_FIFO_CNTXT_SVH__


class uvme_fifo_cntxt_c extends uvm_object;

    virtual uvma_wr_if wr_vif;
    virtual uvma_rd_if rd_vif;

    // Agent context Handle
    uvma_wr_rd_cntxt_c write_cntxt;
    uvma_wr_rd_cntxt_c read_cntxt;

    // Data Monitoring
    // Events

    `uvm_object_utils_begin(uvme_fifo_cntxt_c)
        `uvm_field_object(write_cntxt, UVM_ALL_ON)
        `uvm_field_object(read_cntxt, UVM_ALL_ON)
    `uvm_object_utils_end

    // Constructor
    extern function new(string name="uvme_fifo_cntxt");

endclass : uvme_fifo_cntxt_c


function uvme_fifo_cntxt_c::new(string name="uvme_fifo_cntxt");

    super.new(name);

    write_cntxt = uvma_wr_rd_cntxt_c::type_id::create("write_cntxt");
    read_cntxt = uvma_wr_rd_cntxt_c::type_id::create("read_cntxt");

endfunction : new


`endif // __UVME_FIFO_CNTXT_SVH__
