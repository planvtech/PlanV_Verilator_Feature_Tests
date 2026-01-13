// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`ifndef __UVMA_WR_RD_MON_SVH__
`define __UVMA_WR_RD_MON_SVH__

/** Base Monitor
  * uvm_seq_item
  */

class uvma_wr_rd_base_mon_c#(type SEQ_ITEM = uvm_sequence_item) extends uvm_monitor;

    // objects
    uvma_wr_rd_cfg_c cfg;
    uvma_wr_rd_cntxt_c cntxt;

    // TLM
    uvm_analysis_port #(SEQ_ITEM) ap;

    // Factory
    `ifdef VERILATOR
    `uvm_component_utils(uvma_wr_rd_base_mon_c#(SEQ_ITEM))
    `else
    `uvm_component_param_utils_begin(uvma_wr_rd_base_mon_c#(SEQ_ITEM))
        `uvm_field_object(cfg, UVM_ALL_ON)
        `uvm_field_object(cntxt, UVM_ALL_ON)
    `uvm_component_utils_end
    `endif

    extern function new(string name="uvma_wr_rd_base_mon", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual task run_phase(uvm_phase phase);

    extern virtual task mon_one_item(SEQ_ITEM tr);

endclass : uvma_wr_rd_base_mon_c


function uvma_wr_rd_base_mon_c::new(string name="uvma_wr_rd_base_mon", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


function void uvma_wr_rd_base_mon_c::build_phase(uvm_phase phase);

    super.build_phase(phase);

    `uvm_info("MON", "Entered build_phase", UVM_MEDIUM)

    void'(uvm_config_db#(uvma_wr_rd_cfg_c)::get(this, "", "cfg", cfg));
    if (cfg == null) begin
        `uvm_fatal("CFG", "cfg is null")
    end

    void'(uvm_config_db#(uvma_wr_rd_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("CNTXT", "cntxt is null")
    end

    ap = new("ap", this);

    `uvm_info("MON", "Exiting build_phase", UVM_MEDIUM)

endfunction : build_phase


task uvma_wr_rd_base_mon_c::run_phase(uvm_phase phase);
    
    SEQ_ITEM tr;

    super.run_phase(phase);

    `uvm_info("MON", "Entered run_phase", UVM_MEDIUM)
    
    if (cfg.enabled) begin
        if (cfg.wr_or_rd == WR) begin
            `uvm_info("MON", "WR_Monitor is enabled in Run Phase.", UVM_MEDIUM)
        end
        else begin
            `uvm_info("MON", "RD_Monitor is enabled in Run Phase.", UVM_MEDIUM)
        end

        fork
            begin
                forever begin
                    `ifdef VERILATOR
                    tr = new("tr");
                    `else
                    tr = SEQ_ITEM::type_id::create("tr");
                    `endif
                    mon_one_item(tr);
                    if (tr == null) begin
                        `uvm_info("MON_null", "tr is null", UVM_MEDIUM)
                    end
                    else begin
                        `uvm_info("MON_sb", "tr is not null", UVM_MEDIUM)
                        ap.write(tr);
                    end
                end
            end

            /* TODO
            begin : xx

            end
            */
        join_none
    end

    `uvm_info("MON", "Exiting run_phase", UVM_MEDIUM)

endtask : run_phase


task uvma_wr_rd_base_mon_c::mon_one_item(SEQ_ITEM tr);

endtask : mon_one_item


/** Write Monitor
  * uvma_wr_seq_item_c
  */

class uvma_wr_mon_c extends uvma_wr_rd_base_mon_c#(uvma_wr_seq_item_c);

    `uvm_component_utils(uvma_wr_mon_c)

    extern function new(string name="uvma_wr_mon_c", uvm_component parent=null);
    extern virtual task mon_one_item(uvma_wr_seq_item_c tr);

endclass : uvma_wr_mon_c


function uvma_wr_mon_c::new(string name="uvma_wr_mon_c", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


task uvma_wr_mon_c::mon_one_item(uvma_wr_seq_item_c tr);

    @(posedge cntxt.wr_vif.clk);
    // while(1) begin
    forever begin
        @(posedge cntxt.wr_vif.clk);
        if(cntxt.wr_vif.en) break;
    end
    
    tr.w_data = cntxt.wr_vif.data;
    `uvm_info("WR_MON", " :: mon_one_item", UVM_MEDIUM)

endtask : mon_one_item


/** Read Monitor
  * rd_seq_item
  */

class uvma_rd_mon_c extends uvma_wr_rd_base_mon_c#(uvma_rd_seq_item_c);

    `uvm_component_utils(uvma_rd_mon_c)

    extern function new(string name="uvma_rd_mon_c", uvm_component parent=null);
    extern virtual task mon_one_item(uvma_rd_seq_item_c tr);

endclass : uvma_rd_mon_c


function uvma_rd_mon_c::new(string name="uvma_rd_mon_c", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


task uvma_rd_mon_c::mon_one_item(uvma_rd_seq_item_c tr);

    @(posedge cntxt.rd_vif.clk);
    // while(1) begin
    forever begin
        @(posedge cntxt.rd_vif.clk);
        if(cntxt.rd_vif.en) break;
    end

    tr.r_data = cntxt.rd_vif.data;
    `uvm_info("RD_MON", " :: mon_one_item", UVM_MEDIUM)
    
endtask : mon_one_item


`endif // __UVMA_WR_RD_MON_SVH__
