// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class fifo_virtual_sequencer extends uvm_sequencer;
    r_sequencer r_seqr;
    w_sequencer w_seqr;

    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    `uvm_component_utils(fifo_virtual_sequencer)

    /*
     function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        if (!uvm_config_db#(w_sequencer)::get(this, "w_seqr", "", w_seqr)) begin
        `uvm_fatal("Error", "No w_seqr specified for this instance");
        end
        if (!uvm_config_db#(r_sequencer)::get(this, "r_seqr", "", r_seqr)) begin
        `uvm_fatal("Error", "No r_seqr specified for this instance");
        end
    endfunction
    */
endclass