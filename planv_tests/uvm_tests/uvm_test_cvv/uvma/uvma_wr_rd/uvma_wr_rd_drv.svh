// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

`ifndef __UVMA_WR_RD_DRIVER_SVH__
`define __UVMA_WR_RD_DRIVER_SVH__

/** Base Driver
  * uvm_seq_item
  */

class uvma_wr_rd_base_drv_c #(type SEQ_ITEM = uvm_sequence_item) extends uvm_driver#(
    .REQ(SEQ_ITEM),
    .RSP(SEQ_ITEM)
);

    logic no_tr;

    // objects
    uvma_wr_rd_cfg_c cfg;
    uvma_wr_rd_cntxt_c cntxt;

    // TLM
    uvm_analysis_port #(SEQ_ITEM) ap;

    // Factory
    `uvm_component_param_utils_begin(uvma_wr_rd_base_drv_c#(SEQ_ITEM))
        `ifdef VERILATOR
        `else
        `uvm_field_object(cfg, UVM_ALL_ON)
        `uvm_field_object(cntxt, UVM_ALL_ON)
        `endif
    `uvm_component_utils_end

    extern function new(string name="uvma_wr_rd_base_drv_c", uvm_component parent=null);
    extern virtual function void build_phase(uvm_phase phase);
    extern virtual task run_phase(uvm_phase phase);

    extern virtual task drv_one_item(SEQ_ITEM req);
    extern virtual task drv_nothing();

endclass : uvma_wr_rd_base_drv_c


function uvma_wr_rd_base_drv_c::new(string name="uvma_wr_rd_base_drv_c", uvm_component parent=null);
    
    super.new(name, parent);

endfunction : new


function void uvma_wr_rd_base_drv_c::build_phase(uvm_phase phase);

    super.build_phase(phase);

    `uvm_info("DRV", "Entered build_phase", UVM_MEDIUM)

    void'(uvm_config_db#(uvma_wr_rd_cfg_c)::get(this, "", "cfg", cfg));
    if (cfg == null) begin
        `uvm_fatal("CFG", "cfg is null")
    end
    void'(uvm_config_db#(uvma_wr_rd_cntxt_c)::get(this, "", "cntxt", cntxt));
    if (cntxt == null) begin
        `uvm_fatal("CNTXT", "cntxt is null")
    end

    ap = new("ap", this);

    `uvm_info("DRV", "Exiting build_phase", UVM_MEDIUM)

endfunction : build_phase


task uvma_wr_rd_base_drv_c::run_phase(uvm_phase phase);
    
    SEQ_ITEM req;

    super.run_phase(phase);

    `uvm_info("DRV", "Entered run_phase", UVM_MEDIUM)

    /*
    case (cfg.drv_initial_rst_value)
        UVMA_WRITE_SEQ_ITEM_INITIAL_VALUE_1: cntxt.vif.reset_n = '1;
        UVMA_WRITE_SEQ_ITEM_INITIAL_VALUE_X: cntxt.vif.reset_n = 'X;

        default: begin
            `uvm_fatal("CFG", "cfg.drv_initial_rst_value is not valid")
        end
    endcase
    */
    fork 
        forever begin
            `uvm_info("DRV", "Waiting for a sequence item", UVM_MEDIUM)
            seq_item_port.get_next_item(req);
            no_tr = 1'b0;
            drv_one_item(req);
            no_tr = 1'b1;
            if (req == null) begin
                `uvm_info("DRV_null", "Received null sequence item", UVM_MEDIUM)
            end
            else begin
                ap.write(req); // Send the input item to the analysis port
            end
            seq_item_port.item_done();
        end

        forever begin
            drv_nothing();
        end

    join_none
    `uvm_info("DRV", "Exiting run_phase", UVM_MEDIUM)

endtask : run_phase


task uvma_wr_rd_base_drv_c::drv_one_item(SEQ_ITEM req);

endtask : drv_one_item


task uvma_wr_rd_base_drv_c::drv_nothing();

endtask : drv_nothing


/** Write Driver
  * wr_seq_item_c
  */

class uvma_wr_drv_c extends uvma_wr_rd_base_drv_c#(uvma_wr_seq_item_c);
    
    `uvm_component_utils(uvma_wr_drv_c)

    extern function new(string name="uvma_wr_drv", uvm_component parent=null);
    extern virtual task drv_one_item(uvma_wr_seq_item_c req);
    extern virtual task drv_nothing();

endclass : uvma_wr_drv_c


function uvma_wr_drv_c::new(string name="uvma_wr_drv", uvm_component parent=null);
    
    super.new(name, parent);

endfunction : new


task uvma_wr_drv_c::drv_one_item(uvma_wr_seq_item_c req);
    
    @(posedge cntxt.wr_vif.clk);
    `uvm_info("WR_DRV", "Entered drv_one_item", UVM_MEDIUM)
    while (1) begin
        if (cntxt.wr_vif.full == 1'b1) begin
            cntxt.wr_vif.en <= 1'b0;
            @(posedge cntxt.wr_vif.clk);
        end
        else begin
            cntxt.wr_vif.data <= req.w_data;
            cntxt.wr_vif.en <= 1'b1;
            break;
        end
    end

    @(posedge cntxt.wr_vif.clk);
    cntxt.wr_vif.en <= 1'b0;

endtask : drv_one_item


task uvma_wr_drv_c::drv_nothing();
    
    @(posedge cntxt.wr_vif.clk);
    if (no_tr) begin
        cntxt.wr_vif.en = 1'b0;
    end

endtask : drv_nothing



/** Read Driver
  * rd_seq_item_c
  */

class uvma_rd_drv_c extends uvma_wr_rd_base_drv_c#(uvma_rd_seq_item_c);
    
    `uvm_component_utils(uvma_rd_drv_c)

    extern function new(string name="uvma_rd_drv", uvm_component parent=null);
    extern virtual task drv_one_item(uvma_rd_seq_item_c req);
    extern virtual task drv_nothing();

endclass : uvma_rd_drv_c


function uvma_rd_drv_c::new(string name="uvma_rd_drv", uvm_component parent=null);
    
    super.new(name, parent);

endfunction : new


task uvma_rd_drv_c::drv_one_item(uvma_rd_seq_item_c req);
    
    @(posedge cntxt.rd_vif.clk);
    `uvm_info("RD_DRV", "Entered drv_one_item", UVM_MEDIUM)
    forever begin
        if (cntxt.rd_vif.empty == 1'b1) begin
            cntxt.rd_vif.en <= 1'b0;
            @(posedge cntxt.rd_vif.clk);
        end
        else begin
            cntxt.rd_vif.en <= 1'b1;
            break;
        end
    end

    @(posedge cntxt.rd_vif.clk);
    cntxt.rd_vif.en <= 1'b0;

endtask : drv_one_item


task uvma_rd_drv_c::drv_nothing();

    @(posedge cntxt.rd_vif.clk);
    if (no_tr) begin
        cntxt.rd_vif.en <= 1'b0;
    end

endtask : drv_nothing

`endif // __UVMA_WR_RD_DRV_SVH__
