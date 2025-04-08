// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`ifndef __UVMA_WR_RD_AGENT_SVH__
`define __UVMA_WR_RD_AGENT_SVH__



class uvma_wr_rd_agent_c#(type SEQ_ITEM = uvm_sequence_item) extends uvm_agent;

    // objects
    uvma_wr_rd_cfg_c cfg;
    uvma_wr_rd_cntxt_c cntxt;

    // components
    uvma_wr_rd_base_drv_c#(SEQ_ITEM) drv;
    uvma_wr_rd_base_mon_c#(SEQ_ITEM) mon;
    uvma_wr_rd_base_sqr_c#(SEQ_ITEM) sqr;
    // uvma_wr_rd_cov_c cov_model;
    // uvma_wr_rd_trn_loggers_c trn_loggers;

    // TLM
    uvm_analysis_port #(SEQ_ITEM) drv_ap;
    uvm_analysis_port #(SEQ_ITEM) mon_ap;

    // Fatory
    `uvm_component_param_utils_begin(uvma_wr_rd_agent_c#(SEQ_ITEM))
        `uvm_field_object(cfg, UVM_ALL_ON)
        `uvm_field_object(cntxt, UVM_ALL_ON)
    `uvm_component_utils_end

    // Constructor
    extern function new(string name="uvma_wr_rd_agent", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void connect_phase(uvm_phase phase);

    extern function void get_and_set_cfg();
    extern function void get_and_set_cntxt();
    extern function void retrieve_vifs();
    extern function void create_components();
    extern function void connect_sequencer_and_driver();
    extern function void connect_analysis_ports();
    extern function void connect_cov_model();
    extern function void connect_trn_loggers();

endclass


function uvma_wr_rd_agent_c::new(string name="uvma_wr_rd_agent", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


function void uvma_wr_rd_agent_c::build_phase(uvm_phase phase);

    super.build_phase(phase);
    `uvm_info("AGENT", "Entered build phase.", UVM_MEDIUM)
    get_and_set_cfg();
    get_and_set_cntxt();
    retrieve_vifs();
    create_components();
    `uvm_info("AGENT", "Exiting build phase.", UVM_MEDIUM)

endfunction : build_phase


function void uvma_wr_rd_agent_c::connect_phase(uvm_phase phase);

    super.connect_phase(phase);

    `uvm_info("AGENT", "Entered connect phase.", UVM_MEDIUM)

    connect_sequencer_and_driver();

    connect_analysis_ports();

    if (cfg.cov_model_enabled) begin
        connect_cov_model();
    end
    // if (cfg.trn_loggers_enabled) begin
    //     connect_trn_loggers();
    // end

    `uvm_info("AGENT", "Exiting connect phase.", UVM_MEDIUM)

endfunction : connect_phase


function void uvma_wr_rd_agent_c::get_and_set_cfg();
    
    void'(uvm_config_db#(uvma_wr_rd_cfg_c)::get(this, "", "cfg", cfg));
    if (cfg == null) begin
        `uvm_fatal("CFG", "cfg is null")
    end
    else begin
        uvm_config_db#(uvma_wr_rd_cfg_c)::set(this, "*", "cfg", cfg);
    end

endfunction : get_and_set_cfg


function void uvma_wr_rd_agent_c::get_and_set_cntxt();
    
    void'(uvm_config_db#(uvma_wr_rd_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("CNTXT", "cntxt is null")
    end
    else begin
        uvm_config_db#(uvma_wr_rd_cntxt_c)::set(this, "*", "cntxt", cntxt);
    end

endfunction : get_and_set_cntxt


function void uvma_wr_rd_agent_c::retrieve_vifs();
    
    if (!uvm_config_db#(virtual uvma_wr_if)::get(this, "", "wr_vif", cntxt.wr_vif)) begin
        `uvm_fatal("WR_VIF", "wr_vif is null")
    end

    if (!uvm_config_db#(virtual uvma_rd_if)::get(this, "", "rd_vif", cntxt.rd_vif)) begin
        `uvm_fatal("RD_VIF", "rd_vif is null")
    end

endfunction : retrieve_vifs


function void uvma_wr_rd_agent_c::create_components();

    if (cfg.wr_or_rd == WR) begin
        uvma_wr_rd_base_drv_c#(SEQ_ITEM)::type_id::set_type_override(uvma_wr_drv_c::get_type());
        uvma_wr_rd_base_mon_c#(SEQ_ITEM)::type_id::set_type_override(uvma_wr_mon_c::get_type());
        uvma_wr_rd_base_sqr_c#(SEQ_ITEM)::type_id::set_type_override(uvma_wr_sqr_c::get_type());
    end
    else if (cfg.wr_or_rd == RD) begin
        uvma_wr_rd_base_drv_c#(SEQ_ITEM)::type_id::set_type_override(uvma_rd_drv_c::get_type());
        uvma_wr_rd_base_mon_c#(SEQ_ITEM)::type_id::set_type_override(uvma_rd_mon_c::get_type());
        uvma_wr_rd_base_sqr_c#(SEQ_ITEM)::type_id::set_type_override(uvma_rd_sqr_c::get_type());
    end
    else begin
        `uvm_fatal("AGENT", "cfg.wr_or_rd is not WR or RD")
    end
    drv = uvma_wr_rd_base_drv_c#(SEQ_ITEM)::type_id::create("drv", this);
    sqr = uvma_wr_rd_base_sqr_c#(SEQ_ITEM)::type_id::create("sqr", this);
    mon = uvma_wr_rd_base_mon_c#(SEQ_ITEM)::type_id::create("mon", this);

    `uvm_info("AGENT", $sformatf("type of mon := %s", $typename(mon)), UVM_MEDIUM)
    `uvm_info("AGENT", $sformatf("type of mon := %s", mon.get_type_name()), UVM_MEDIUM)

    // cov_model = uvma_wr_rd_cov_c::type_id::create("cov_model", this);
    // trn_loggers = uvma_wr_rd_trn_loggers_c::type_id::create("trn_loggers", this);

endfunction : create_components


function void uvma_wr_rd_agent_c::connect_sequencer_and_driver();
    
    drv.seq_item_port.connect(sqr.seq_item_export);

endfunction : connect_sequencer_and_driver


function void uvma_wr_rd_agent_c::connect_analysis_ports();
    
    if (cfg.is_active == UVM_ACTIVE) begin
        drv_ap = drv.ap;
        mon_ap = mon.ap;
    end 
    else if (cfg.is_active == UVM_PASSIVE) begin
        mon_ap = mon.ap;
    end
    else begin
        `uvm_fatal("AGENT", "cfg.is_active is not UVM_ACTIVE or UVM_PASSIVE")
    end

endfunction : connect_analysis_ports


function void uvma_wr_rd_agent_c::connect_cov_model();
    
    // TODO

endfunction : connect_cov_model

function void uvma_wr_rd_agent_c::connect_trn_loggers();
    
    // TODO

endfunction : connect_trn_loggers

`endif // __UVMA_WR_RD_AGENT_SVH__
