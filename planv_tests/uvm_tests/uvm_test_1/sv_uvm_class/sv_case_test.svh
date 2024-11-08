// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class case0_test extends fifo_base_test;

    case0_sequence seq0 = new("seq0");
    function new(string name, uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        $display("Case0 Starts!!!");
        seq0.start(env.v_seqr);
        $display("Case0 Ends!!!");
        phase.drop_objection(this);
    endtask

    `uvm_component_utils(case0_test)

endclass