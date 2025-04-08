// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_RESET_VSEQ_SVH__
`define __UVME_FIFO_RESET_VSEQ_SVH__


class uvme_fifo_reset_vseq_c extends uvme_fifo_base_vseq_c;
    
    rand int unsigned num_clk_before_reset; // Number of clock cycles between start of clock and reset assert
    rand int unsigned rst_deassert_period;  // Time delta between reset assert and deassert, in picoseconds (ps)
    rand int unsigned post_rst_wait_period; // Time delta between reset deassert and end of virtual sequence, in picoseconds (ps)

    `uvm_object_utils_begin(uvme_fifo_reset_vseq_c)
        `uvm_field_int(num_clk_before_reset, UVM_ALL_ON)
        `uvm_field_int(rst_deassert_period, UVM_ALL_ON)
        `uvm_field_int(post_rst_wait_period, UVM_ALL_ON)
    `uvm_object_utils_end

    constraint default_cons {
        soft num_clk_before_reset == 10;
        soft rst_deassert_period == 1000;
        soft post_rst_wait_period == 1000;
    }
    
    // Constructor
    extern function new(string name="uvme_fifo_reset_vseq");

    extern virtual task body();

endclass : uvme_fifo_reset_vseq_c


function uvme_fifo_reset_vseq_c::new(string name="uvme_fifo_reset_vseq");
    
    super.new(name);

endfunction : new


task uvme_fifo_reset_vseq_c::body();
    
    

endtask : body
