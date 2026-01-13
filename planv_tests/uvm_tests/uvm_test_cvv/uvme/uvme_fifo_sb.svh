// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_SB_SVH__
`define __UVME_FIFO_SB_SVH__

`uvm_analysis_imp_decl(_wr_act)
`uvm_analysis_imp_decl(_rd_act)
`uvm_analysis_imp_decl(_wr_exp)
`uvm_analysis_imp_decl(_rd_exp)

class uvme_fifo_sb_c extends uvm_scoreboard;

    // Objects
    uvme_fifo_cntxt_c cntxt;
    uvme_fifo_cfg_c cfg;

    // Queues
    uvma_wr_seq_item_c wr_act_queue[$];
    uvma_rd_seq_item_c rd_act_queue[$];
    uvma_wr_seq_item_c wr_exp_queue[$];
    uvma_rd_seq_item_c rd_exp_queue[$];

    // TLM 
    uvm_analysis_imp_wr_act#(uvma_wr_seq_item_c, uvme_fifo_sb_c) wr_act_imp;
    uvm_analysis_imp_rd_act#(uvma_rd_seq_item_c, uvme_fifo_sb_c) rd_act_imp;

    uvm_analysis_imp_wr_exp#(uvma_wr_seq_item_c, uvme_fifo_sb_c) wr_exp_imp;
    uvm_analysis_imp_rd_exp#(uvma_rd_seq_item_c, uvme_fifo_sb_c) rd_exp_imp;

    // Components
    // TODO Add sub-scoreboards
    `ifdef VERILATOR
    `uvm_component_utils(uvme_fifo_sb_c)
    `else
    `uvm_component_utils_begin(uvme_fifo_sb_c)
        `uvm_field_object(cntxt, UVM_ALL_ON)
        `uvm_field_object(cfg, UVM_ALL_ON)
    `uvm_component_utils_end
    `endif

    // Constructor
    extern function new(string name="uvme_fifo_sb_c", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual task run_phase(uvm_phase phase);
    
    extern virtual function void assign_cfg();
    extern virtual function void assign_cntxt();
    extern virtual function void create_sub_scoreboards();

    extern virtual task process_write();
    extern virtual task process_read();

    extern virtual function void write_wr_act(uvma_wr_seq_item_c tr);
    extern virtual function void write_rd_act(uvma_rd_seq_item_c tr);
    extern virtual function void write_wr_exp(uvma_wr_seq_item_c tr);
    extern virtual function void write_rd_exp(uvma_rd_seq_item_c tr);

endclass : uvme_fifo_sb_c



function uvme_fifo_sb_c::new(string name="uvme_fifo_sb_c", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


function void uvme_fifo_sb_c::build_phase(uvm_phase phase);

    super.build_phase(phase);
    
    `uvm_info("SB", "Entered build_phase", UVM_MEDIUM)

    void'(uvm_config_db#(uvme_fifo_cfg_c)::get(this, "", "cfg", cfg));
    if (cfg == null) begin
        `uvm_fatal("CFG", "cfg is null")
    end

    void'(uvm_config_db#(uvme_fifo_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("CNTXT", "cntxt is null")
    end

    assign_cfg();
    assign_cntxt();
    create_sub_scoreboards();

    wr_act_imp = new("wr_act_imp", this);
    rd_act_imp = new("rd_act_imp", this);
    wr_exp_imp = new("wr_exp_imp", this);
    rd_exp_imp = new("rd_exp_imp", this);

    `uvm_info("SB", "Exiting build_phase", UVM_MEDIUM)

endfunction : build_phase


function void uvme_fifo_sb_c::assign_cfg();

    // TODO Assign cfg to sub-scoreboards

endfunction : assign_cfg


function void uvme_fifo_sb_c::assign_cntxt();

    // TODO Assign cntxt to sub-scoreboards

endfunction : assign_cntxt


function void uvme_fifo_sb_c::create_sub_scoreboards();

    // TODO Create sub-scoreboards

endfunction : create_sub_scoreboards


task uvme_fifo_sb_c::run_phase(uvm_phase phase);

    super.run_phase(phase);
    
    `uvm_info("SB", "Entered run_phase", UVM_MEDIUM)

    fork
        begin
            process_write();
        end
        begin
            process_read();
        end
    join_none
    `uvm_info("SB", "Exiting run_phase", UVM_MEDIUM)

endtask : run_phase


task uvme_fifo_sb_c::process_write();

    uvma_wr_seq_item_c wr_act_tr;
    uvma_wr_seq_item_c wr_exp_tr;

    while (1) begin
        @(posedge cntxt.wr_vif.clk);
        while ((wr_act_queue.size() > 0) && (wr_act_queue[0] == null)) begin
            `uvm_info("SB", "Popped null transaction from wr_act_queue", UVM_MEDIUM)
            wr_act_queue.pop_front();
        end
        while ((wr_exp_queue.size() > 0) && (wr_exp_queue[0] == null)) begin
            `uvm_info("SB", "Popped null transaction from wr_exp_queue", UVM_MEDIUM)
            wr_exp_queue.pop_front();
        end
        if ((wr_act_queue.size() > 0) && (wr_exp_queue.size() > 0)) begin

            wr_act_tr = wr_act_queue.pop_front();
            wr_exp_tr = wr_exp_queue.pop_front();
            // wr_act_tr.print();
            // wr_exp_tr.print();
            if (wr_act_tr.w_full != wr_exp_tr.w_full) begin
                `uvm_error("SCB", $sformatf("w_full mismatch: Act_%0d != Exp_%0d", wr_act_tr.w_full, wr_exp_tr.w_full))
            end
            
        end
    end

endtask : process_write


task uvme_fifo_sb_c::process_read();

    uvma_rd_seq_item_c rd_act_tr;
    uvma_rd_seq_item_c rd_exp_tr;
    
    while (1) begin
        @(posedge cntxt.rd_vif.clk);
        while ((rd_act_queue.size() > 0) && (rd_act_queue[0] == null)) begin
            `uvm_info("SB", "Popped null transaction from rd_act_queue", UVM_MEDIUM)
            rd_act_queue.pop_front();
        end
        while ((rd_exp_queue.size() > 0) && (rd_exp_queue[0] == null)) begin
            `uvm_info("SB", "Popped null transaction from rd_exp_queue", UVM_MEDIUM)
            rd_exp_queue.pop_front();
        end
        if ((rd_act_queue.size() > 0) && (rd_exp_queue.size() > 0)) begin
            
            rd_act_tr = rd_act_queue.pop_front();
            rd_exp_tr = rd_exp_queue.pop_front();
            if (rd_act_tr.r_empty != rd_exp_tr.r_empty) begin
                `uvm_error("SCB", $sformatf("r_empty mismatch: Act_%0d != Exp_%0d", rd_act_tr.r_empty, rd_exp_tr.r_empty))
            end
            if (rd_act_tr.r_data != rd_exp_tr.r_data) begin
                `uvm_error("SCB", $sformatf("r_data mismatch: Act_%0d != Exp_%0d", rd_act_tr.r_data, rd_exp_tr.r_data))
            end
            // rd_act_tr.print();
            // rd_exp_tr.print();
            
        end
    end

endtask : process_read


function void uvme_fifo_sb_c::write_wr_act(uvma_wr_seq_item_c tr);

    wr_act_queue.push_back(tr);

endfunction : write_wr_act


function void uvme_fifo_sb_c::write_rd_act(uvma_rd_seq_item_c tr);

    rd_act_queue.push_back(tr);

endfunction : write_rd_act


function void uvme_fifo_sb_c::write_wr_exp(uvma_wr_seq_item_c tr);

    wr_exp_queue.push_back(tr);

endfunction : write_wr_exp


function void uvme_fifo_sb_c::write_rd_exp(uvma_rd_seq_item_c tr);

    rd_exp_queue.push_back(tr);

endfunction : write_rd_exp


`endif // __UVME_FIFO_SB_SVH__
