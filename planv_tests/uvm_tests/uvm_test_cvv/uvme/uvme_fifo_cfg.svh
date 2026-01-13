// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVME_FIFO_CFG_SVH__
`define __UVME_FIFO_CFG_SVH__


class uvme_fifo_cfg_c extends uvm_object;

    // Common Options
    rand bit enabled;
    rand uvm_active_passive_enum is_active;
    rand bit scoreboard_enabled;
    rand bit cov_model_enabled;
    // rand bit trn_log_enabled;

    // Implementation Options


    // Agent cfg handles
    rand uvma_wr_rd_cfg_c write_cfg;
    rand uvma_wr_rd_cfg_c read_cfg;

    `uvm_object_utils_begin(uvme_fifo_cfg_c)
        `uvm_field_int(enabled, UVM_ALL_ON)
        `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_ALL_ON)
        `uvm_field_int(scoreboard_enabled, UVM_ALL_ON)
        `uvm_field_int(cov_model_enabled, UVM_ALL_ON)
        `uvm_field_object(read_cfg, UVM_ALL_ON)
        `uvm_field_object(write_cfg, UVM_ALL_ON)
    `uvm_object_utils_end

    `ifndef VERILATOR
    constraint defaults_con {
        soft enabled == 0;
        soft is_active == UVM_PASSIVE;
        soft scoreboard_enabled == 1;
        soft cov_model_enabled == 1;
    }
    `endif

    constraint agent_cfg_cons {
        if (enabled) {
            write_cfg.enabled == 1;
            read_cfg.enabled == 1;
        }

        if (is_active == UVM_ACTIVE) {
            write_cfg.is_active == UVM_ACTIVE;
            read_cfg.is_active == UVM_ACTIVE;
        }

        write_cfg.wr_or_rd == WR;
        read_cfg.wr_or_rd == RD;

        // if (cov_model_enabled) {
            // write_cfg.cov == 1;
            // write_cfg.is_active == UVM_PASSIVE;
        // }
    }

    // Constructor
    extern function new(string name="uvme_fifo_cfg");
    extern function void pre_randomize();
    
endclass : uvme_fifo_cfg_c


function uvme_fifo_cfg_c::new(string name="uvme_fifo_cfg");

    super.new(name);

    write_cfg = uvma_wr_rd_cfg_c::type_id::create("write_cfg");
    read_cfg = uvma_wr_rd_cfg_c::type_id::create("read_cfg");

endfunction : new


function void uvme_fifo_cfg_c::pre_randomize();
    
    // if ($test$plusargs("uvme_fifo_cfg")) begin
    // end

endfunction : pre_randomize


`endif // __UVME_FIFO_CFG_SVH__
