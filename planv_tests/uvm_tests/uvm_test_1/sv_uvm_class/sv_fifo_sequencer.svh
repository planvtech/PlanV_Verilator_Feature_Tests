// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`ifdef VERILATOR
class w_sequencer extends uvm_sequencer #(w_sequence_item,w_sequence_item);
`else
class w_sequencer extends uvm_sequencer #(w_sequence_item);
`endif

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    `uvm_component_utils(w_sequencer)
endclass

`ifdef VERILATOR
class r_sequencer extends uvm_sequencer #(r_sequence_item,r_sequence_item);
`else
class r_sequencer extends uvm_sequencer #(r_sequence_item);
`endif

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    `uvm_component_utils(r_sequencer)

endclass