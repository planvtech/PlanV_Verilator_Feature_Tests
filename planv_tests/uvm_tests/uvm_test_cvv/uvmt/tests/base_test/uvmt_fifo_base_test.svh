// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMT_FIFO_BASE_TEST_SVH__
`define __UVMT_FIFO_BASE_TEST_SVH__


class uvmt_fifo_base_test_c extends uvm_test;

    // Objects
    rand uvmt_fifo_test_cfg_c           test_cfg;
    rand uvmt_fifo_test_randvars_c      test_randvars;
    rand uvme_fifo_cfg_c                env_cfg;
    rand uvme_fifo_cntxt_c              env_cntxt;

    // Components
    uvme_fifo_env_c                  env;
    uvme_fifo_vsqr_c                vsqr;

    // Handles testbench interfaces
    virtual uvmt_fifo_clk_gen_if rd_clk_gen_vif;
    virtual uvmt_fifo_clk_gen_if wr_clk_gen_vif;

    int success;

    // Default Sequence
    // rand uvme_fifo_random_vseq_c   random_vseq;     

    // Factory
    `ifdef VERILATOR
    `uvm_component_utils(uvmt_fifo_base_test_c)
    `else
    `uvm_component_utils_begin(uvmt_fifo_base_test_c)
        `uvm_field_object(test_cfg, UVM_ALL_ON)
        `uvm_field_object(test_randvars, UVM_ALL_ON)
        `uvm_field_object(env_cfg, UVM_ALL_ON)
        `uvm_field_object(env_cntxt, UVM_ALL_ON)
    `uvm_component_utils_end
    `endif

    constraint env_cfg_con {
        env_cfg.enabled == 1;
        env_cfg.is_active == UVM_ACTIVE;
        env_cfg.scoreboard_enabled == 1;
        env_cfg.cov_model_enabled == 0;
    }

    // Constructor
    extern function new(string name="uvmt_fifo_base_test", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void connect_phase(uvm_phase phase);
    extern virtual task run_phase(uvm_phase phase);
    extern virtual function void report_phase(uvm_phase phase);

    extern function void retrieve_vifs();
    extern virtual function void create_cfg_and_cntxt();
    extern virtual function void randomize_test();
    extern virtual function void assign_cfg();
    // extern virtual function void create_cntxt();
    extern virtual function void assign_cntxt();
    extern virtual function void create_env();
    extern virtual function void create_components();
    extern virtual task watchdog_timer();

endclass : uvmt_fifo_base_test_c


function uvmt_fifo_base_test_c::new(string name="uvmt_fifo_base_test", uvm_component parent=null);

    super.new(name, parent);

    // random_vseq = uvme_fifo_random_vseq_c::type_id::create("random_vseq", vsqr);

endfunction : new


function void uvmt_fifo_base_test_c::build_phase(uvm_phase phase);

    super.build_phase(phase);

    `uvm_info("TEST", "Entered build_phase", UVM_MEDIUM)

    retrieve_vifs();
    create_cfg_and_cntxt();
    randomize_test();
    `uvm_info("TEST", $sformatf("##### After randomize: env_cfg.enabled=%0d", this.env_cfg.enabled), UVM_LOW)
    assign_cfg();
    // create_cntxt();
    assign_cntxt();
    create_env();
    create_components();

    `uvm_info("TEST", "Exiting build_phase", UVM_MEDIUM)

endfunction : build_phase


function void uvmt_fifo_base_test_c::connect_phase(uvm_phase phase);

    super.connect_phase(phase);

    `uvm_info("TEST", "Entered connect_phase", UVM_MEDIUM)

    vsqr = env.vsequencer;

    `uvm_info("TEST", "Exiting connect_phase", UVM_MEDIUM)

endfunction : connect_phase


task uvmt_fifo_base_test_c::run_phase(uvm_phase phase);

    // CRITICAL: Raise objection BEFORE super.run_phase() to prevent race condition
    // If we raise it after super.run_phase(), UVM might see all components exited
    // (due to fork...join_none in drivers/monitors) and decide to end the phase
    phase.raise_objection(this, "Test is running");
    `uvm_info("TEST", "Raised objection BEFORE super.run_phase()", UVM_LOW)

    super.run_phase(phase);

    `uvm_info("TEST", "Entered run_phase", UVM_MEDIUM)

    // random_vseq.start(vsqr);
    `uvm_info("TEST", "About to wait 2000ns", UVM_LOW)
    #2000ns;
    `uvm_info("TEST", "Finished waiting 2000ns", UVM_LOW)

    watchdog_timer();

    // Drop objection to allow phase to end
    phase.drop_objection(this, "Test completed");
    `uvm_info("TEST", "Dropped objection", UVM_LOW)

    `uvm_info("TEST", "Exiting run_phase", UVM_MEDIUM)

endtask : run_phase


function void uvmt_fifo_base_test_c::report_phase(uvm_phase phase);

    super.report_phase(phase);
    `uvm_info("TEST", "Entered report_phase, set sim_finished high to notify the testbench.", UVM_MEDIUM)
    uvm_config_db#(bit)::set(null, "", "sim_finished", 1);

endfunction : report_phase


function void uvmt_fifo_base_test_c::retrieve_vifs();

    if (!uvm_config_db#(virtual uvmt_fifo_clk_gen_if)::get(this, "", "wr_clk_gen_vif", wr_clk_gen_vif)) begin
        `uvm_fatal("VIF", "wr_clk_gen_vif is null")
    end

    if (!uvm_config_db#(virtual uvmt_fifo_clk_gen_if)::get(this, "", "rd_clk_gen_vif", rd_clk_gen_vif)) begin
        `uvm_fatal("VIF", "rd_clk_gen_vif is null")
    end

endfunction : retrieve_vifs


function void uvmt_fifo_base_test_c::create_cfg_and_cntxt();

    test_cfg = uvmt_fifo_test_cfg_c ::type_id::create("test_cfg");
    env_cfg  = uvme_fifo_cfg_c      ::type_id::create("env_cfg");

    test_randvars = uvmt_fifo_test_randvars_c   ::type_id::create("test_randvars");
    env_cntxt     = uvme_fifo_cntxt_c           ::type_id::create("env_cntxt");

endfunction : create_cfg_and_cntxt


function void uvmt_fifo_base_test_c::randomize_test();

    if (!this.randomize()) begin
       `uvm_fatal("RANDOMIZE", "Randomization failed")
    end

endfunction : randomize_test


function void uvmt_fifo_base_test_c::assign_cfg();

    uvm_config_db#(uvme_fifo_cfg_c)::set(this, "env", "cfg", env_cfg);

endfunction : assign_cfg


function void uvmt_fifo_base_test_c::assign_cntxt();

    uvm_config_db#(uvme_fifo_cntxt_c)::set(this, "env", "cntxt", env_cntxt);

endfunction : assign_cntxt


function void uvmt_fifo_base_test_c::create_env();

    env = uvme_fifo_env_c::type_id::create("env", this);

endfunction : create_env


function void uvmt_fifo_base_test_c::create_components();

    // TODO

endfunction : create_components


task uvmt_fifo_base_test_c::watchdog_timer();

    fork
        begin
            # 1ns; // Give verilator time to start up
            $display("\n%m: Watchdog timer will wait for %0dns\n", test_cfg.watchdog_timeout * 1ns);
            # (test_cfg.watchdog_timeout * 1ns);
            `uvm_fatal("TIMEOUT", "Test timed out")
        end
    join_none

endtask : watchdog_timer


`endif  // __UVMT_FIFO_BASE_TEST_SVH__
