// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_ENV_SVH__
`define __UVME_FIFO_ENV_SVH__


class uvme_fifo_env_c extends uvm_env;

    // Objects
    uvme_fifo_cfg_c cfg;
    uvme_fifo_cntxt_c cntxt;

    // Components
    // uvme_fifo_cov_model_c cov_model;
    uvme_fifo_prdr_c predictor;
    uvme_fifo_sb_c scoreboard;
    uvme_fifo_vsqr_c vsequencer;

    // Agents
    `ifdef VERILATOR
    uvma_wr_rd_agent_c #(uvma_wr_seq_item_c) write_agent;
    uvma_wr_rd_agent_c #(uvma_rd_seq_item_c) read_agent;
    `else
    write_agent_t write_agent;
    read_agent_t read_agent;
    `endif

    `ifdef VERILATOR
    `uvm_component_utils(uvme_fifo_env_c)
    `else
    `uvm_component_utils_begin(uvme_fifo_env_c)
        `uvm_field_object(cfg, UVM_ALL_ON)
        `uvm_field_object(cntxt, UVM_ALL_ON)
    `uvm_component_utils_end
    `endif

    extern function new(string name="uvme_fifo_env", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void connect_phase(uvm_phase phase);
    extern virtual function void end_of_elaboration_phase(uvm_phase phase);
    extern virtual task run_phase(uvm_phase phase);

    extern virtual function void retrieve_vifs();
    extern virtual function void assign_cfg();
    extern virtual function void assign_cntxt();
    extern virtual function void create_env_components();
    extern virtual function void create_agents();
    extern virtual function void create_vsequencer();
    extern virtual function void create_cov_model();
    extern virtual function void connect_predictor();
    extern virtual function void connect_scoreboard();
    extern virtual function void connect_cov_model();
    extern virtual function void assemble_vsequencer();

endclass : uvme_fifo_env_c


function uvme_fifo_env_c::new(string name="uvme_fifo_env", uvm_component parent=null);

    super.new(name, parent);

endfunction : new


function void uvme_fifo_env_c::build_phase(uvm_phase phase);

    super.build_phase(phase);

    `uvm_info("ENV", "Entered build phase.", UVM_MEDIUM)

    void'(uvm_config_db#(uvme_fifo_cfg_c)::get(this, "", "cfg", cfg));
    if (cfg == null) begin
        `uvm_fatal("ENV_CFG", "cfg is null")
    end

    if (cfg.enabled) begin
        $display("ENV: cfg is enabled in build_phase.");
        void'(uvm_config_db#(uvme_fifo_cntxt_c)::get(this, "", "cntxt", cntxt));
        if (cntxt == null) begin
            `uvm_info("CNTXT", "cntxt is null", UVM_MEDIUM)
            cntxt = uvme_fifo_cntxt_c::type_id::create("cntxt");
        end

        retrieve_vifs();
        assign_cfg();
        assign_cntxt();
        create_agents();
        create_env_components();

        if (cfg.is_active) begin
            create_vsequencer();
        end

        if (cfg.cov_model_enabled) begin
            create_cov_model();
        end
    end

    `uvm_info("ENV", "Exiting build phase.", UVM_MEDIUM)

endfunction : build_phase


function void uvme_fifo_env_c::connect_phase(uvm_phase phase);

    super.connect_phase(phase);
    
    `uvm_info("ENV", "Entered connect phase.", UVM_MEDIUM)

    if (cfg.enabled) begin

        if (cfg.scoreboard_enabled) begin
            `uvm_info("ENV", "scoreboard_enabled is true, connecting predictor and scoreboard.", UVM_MEDIUM)
            connect_predictor();
            connect_scoreboard();
            predictor.wr_output_port.connect(scoreboard.wr_exp_imp);
            predictor.rd_output_port.connect(scoreboard.rd_exp_imp);
        end
        
        if (cfg.is_active) begin
            assemble_vsequencer();
        end

        if (cfg.cov_model_enabled) begin
            connect_cov_model();
        end
    end

    `uvm_info("ENV", "Exiting connect phase.", UVM_MEDIUM)

endfunction : connect_phase


task uvme_fifo_env_c::run_phase(uvm_phase phase);

    uvme_fifo_random_vseq_c random_vseq;

    super.run_phase(phase);

    `uvm_info("ENV", "Entered run phase.", UVM_MEDIUM)
    // phase.raise_objection(this);
    if (cfg.is_active == UVM_ACTIVE) begin
        random_vseq = uvme_fifo_random_vseq_c::type_id::create("random_vseq");
        random_vseq.start(vsequencer);
    end
    // phase.drop_objection(this);
    `uvm_info("ENV", "Exiting run phase.", UVM_MEDIUM)

endtask : run_phase


function void uvme_fifo_env_c::end_of_elaboration_phase(uvm_phase phase);

    super.end_of_elaboration_phase(phase);
    // `uvm_info("ENV", "Entered end_of_elaboration phase.", UVM_MEDIUM)
    // if (cfg.enabled) begin
        // `uvm_info("CFG", "cfg is not null", UVM_MEDIUM)
    // end
    // `uvm_info("ENV", "Exiting end_of_elaboration phase.", UVM_MEDIUM)
endfunction : end_of_elaboration_phase


function void uvme_fifo_env_c::retrieve_vifs();

    if (cfg.enabled) begin
        if (!uvm_config_db#(virtual uvma_wr_if)::get(this, "", "wr_vif", cntxt.wr_vif)) begin
            `uvm_fatal("wr_vif", "virtual interface must be set for wr_vif!")
        end

        if (!uvm_config_db#(virtual uvma_rd_if)::get(this, "", "rd_vif", cntxt.rd_vif)) begin
            `uvm_fatal("rd_vif", "virtual interface must be set for rd_vif!")
        end
    end
    else begin
        `uvm_info("ENV", "cfg is null, skip retrieving vifs.", UVM_MEDIUM)
    end


endfunction : retrieve_vifs


function void uvme_fifo_env_c::assign_cfg();

    uvm_config_db#(uvme_fifo_cfg_c)::set(this, "*", "cfg", cfg);
    uvm_config_db#(uvma_wr_rd_cfg_c)::set(this, "*write_agent", "cfg", cfg.write_cfg);
    uvm_config_db#(uvma_wr_rd_cfg_c)::set(this, "*read_agent", "cfg", cfg.read_cfg);

endfunction : assign_cfg


function void uvme_fifo_env_c::assign_cntxt();

    uvm_config_db#(uvme_fifo_cntxt_c)::set(this, "*", "cntxt", cntxt);
    uvm_config_db#(uvma_wr_rd_cntxt_c)::set(this, "*write_agent", "cntxt", cntxt.write_cntxt);
    uvm_config_db#(uvma_wr_rd_cntxt_c)::set(this, "*read_agent", "cntxt", cntxt.read_cntxt);

endfunction : assign_cntxt


function void uvme_fifo_env_c::create_agents();

    `ifdef VERILATOR
    write_agent = uvma_wr_rd_agent_c#(uvma_wr_seq_item_c)::type_id::create("write_agent", this);
    read_agent = uvma_wr_rd_agent_c#(uvma_rd_seq_item_c)::type_id::create("read_agent", this);
    `else
    write_agent = write_agent_t::type_id::create("write_agent", this);
    read_agent = read_agent_t::type_id::create("read_agent", this);
    `endif

endfunction : create_agents


function void uvme_fifo_env_c::create_env_components();

    if (cfg.scoreboard_enabled) begin
        predictor = uvme_fifo_prdr_c::type_id::create("predictor", this);
        scoreboard = uvme_fifo_sb_c::type_id::create("scoreboard", this);
    end

endfunction : create_env_components


function void uvme_fifo_env_c::create_vsequencer();

    vsequencer = uvme_fifo_vsqr_c::type_id::create("vsequencer", this);

endfunction : create_vsequencer


function void uvme_fifo_env_c::create_cov_model();

    // cov_model = uvme_fifo_cov_model_c::type_id::create("cov_model", this);

endfunction : create_cov_model


function void uvme_fifo_env_c::connect_predictor();

    write_agent.drv_ap.connect(predictor.wr_input_imp);
    read_agent.drv_ap.connect(predictor.rd_input_imp);

endfunction : connect_predictor


function void uvme_fifo_env_c::connect_scoreboard();

    write_agent.mon_ap.connect(scoreboard.wr_act_imp);
    read_agent.mon_ap.connect(scoreboard.rd_act_imp);

endfunction : connect_scoreboard


function void uvme_fifo_env_c::connect_cov_model();

    // TODO

endfunction : connect_cov_model


function void uvme_fifo_env_c::assemble_vsequencer();

    vsequencer.write_sqr = write_agent.sqr;
    vsequencer.read_sqr = read_agent.sqr;

endfunction : assemble_vsequencer


`endif // __UVME_FIFO_ENV_SVH__
