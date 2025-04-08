// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_PRDR_SVH__
`define __UVME_FIFO_PRDR_SVH__

`uvm_analysis_imp_decl(_wr_input)
`uvm_analysis_imp_decl(_rd_input)

class uvme_fifo_prdr_c extends uvm_component;

    // Objects
    uvme_fifo_cfg_c cfg;
    uvme_fifo_cntxt_c cntxt;

    // TLM
    uvm_analysis_imp_wr_input #(uvma_wr_seq_item_c, uvme_fifo_prdr_c) wr_input_imp;
    uvm_analysis_imp_rd_input #(uvma_rd_seq_item_c, uvme_fifo_prdr_c) rd_input_imp;

    uvm_analysis_port #(uvma_wr_seq_item_c) wr_output_port;
    uvm_analysis_port #(uvma_rd_seq_item_c) rd_output_port;

    // Queues
    uvma_wr_seq_item_c wr_queue[$];
    uvma_rd_seq_item_c rd_queue[$];

    // Fifo Model
    logic[7:0] fifo[$];
    int fifo_depth = 16;

    `uvm_component_utils_begin(uvme_fifo_prdr_c)
        `ifdef VERILATOR
        `else
        `uvm_field_object(cfg, UVM_ALL_ON)
        `uvm_field_object(cntxt, UVM_ALL_ON)
        `endif
    `uvm_component_utils_end

    // Constructor
    extern function new(string name="uvme_fifo_prdr_c", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void connect_phase(uvm_phase phase);
    extern virtual task run_phase(uvm_phase phase);

    extern virtual task process_write(uvma_wr_seq_item_c tr);
    extern virtual task process_read(uvma_rd_seq_item_c tr);

    extern virtual function void write_wr_input(uvma_wr_seq_item_c tr);
    extern virtual function void write_rd_input(uvma_rd_seq_item_c tr);

endclass : uvme_fifo_prdr_c


function uvme_fifo_prdr_c::new(string name="uvme_fifo_prdr_c", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


function void uvme_fifo_prdr_c::build_phase(uvm_phase phase);

    super.build_phase(phase);

    `uvm_info("PRDR", "Entered build_phase", UVM_MEDIUM)

    void'(uvm_config_db#(uvme_fifo_cfg_c)::get(this, "", "cfg", cfg));
    if (cfg == null) begin
        `uvm_fatal("CFG", "cfg is null")
    end

    void'(uvm_config_db#(uvme_fifo_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("CNTXT", "cntxt is null")
    end

    // Build Input TLM Objects
    wr_input_imp = new("wr_input_imp", this);
    rd_input_imp = new("rd_input_imp", this);

    wr_output_port = new("wr_output_port", this);
    rd_output_port = new("rd_output_port", this);

    `uvm_info("PRDR", "Exiting build_phase", UVM_MEDIUM)

endfunction : build_phase


function void uvme_fifo_prdr_c::connect_phase(uvm_phase phase);

    super.connect_phase(phase);

    `uvm_info("PRDR", "Entered connect_phase", UVM_MEDIUM)

    // Connect TLM

    `uvm_info("PRDR", "Exiting connect_phase", UVM_MEDIUM)

endfunction : connect_phase


task uvme_fifo_prdr_c::run_phase(uvm_phase phase);

    uvma_wr_seq_item_c wr_tr;
    uvma_rd_seq_item_c rd_tr;

    super.run_phase(phase);

    `uvm_info("PRDR", "Entered run_phase", UVM_MEDIUM)

    fork
        process_write(wr_tr);
        process_read(rd_tr);
    join_none

    `uvm_info("PRDR", "Exiting run_phase", UVM_MEDIUM)

endtask : run_phase


// Get value from the queue and process it
task uvme_fifo_prdr_c::process_write(uvma_wr_seq_item_c tr);

    forever begin
        @(posedge cntxt.wr_vif.clk);
        if (wr_queue.size() > 0) begin
            `uvm_info("WR_PRDR", "queue is not empty so process_write", UVM_MEDIUM)
            tr = wr_queue.pop_front();
            if (fifo.size() >= fifo_depth) begin
                tr.w_full = 1'b1;
            end
            else begin 
                tr.w_full = 1'b0;
                if (tr.w_en) begin
                    fifo.push_back(tr.w_data);
                end
            end
            if (tr == null) begin
                `uvm_info("WR_PRDR_null", "tr is null", UVM_MEDIUM)
            end
            else begin
                wr_output_port.write(tr);
            end
            // tr.print();
        end
    end

endtask : process_write


// Get value from the queue and process it
task uvme_fifo_prdr_c::process_read(uvma_rd_seq_item_c tr);
    
    forever begin
        @(posedge cntxt.rd_vif.clk);

        if (rd_queue.size() > 0) begin
            `uvm_info("RD_PRDR", "queue is not empty so process_read", UVM_MEDIUM)
            tr = rd_queue.pop_front();
            if (fifo.size() <= 0) begin
                tr.r_empty = 1'b1;
            end
            else begin 
                tr.r_empty = 1'b0;
                if (tr.r_en) begin
                    tr.r_data = fifo.pop_front();
                end
            end
            if (tr == null) begin
                `uvm_info("RD_PRDR_null", "tr is null", UVM_MEDIUM)
            end
            else begin
                rd_output_port.write(tr);
            end
            // tr.print();
        end
    end

endtask : process_read


function void uvme_fifo_prdr_c::write_wr_input(uvma_wr_seq_item_c tr);

    wr_queue.push_back(tr);

endfunction : write_wr_input


function void uvme_fifo_prdr_c::write_rd_input(uvma_rd_seq_item_c tr);

    rd_queue.push_back(tr);

endfunction : write_rd_input


`endif // __UVME_FIFO_PRDR_SVH__
