// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMT_FIFO_TEST_CFG_SVH__
`define __UVMT_FIFO_TEST_CFG_SVH__


class uvmt_fifo_test_cfg_c extends uvm_object;

    // rand int unsigned startup_timeout;
    rand int unsigned watchdog_timeout;

    // Factory & Field
    `uvm_object_utils_begin(uvmt_fifo_test_cfg_c)
        // `uvm_field_int(startup_timeout, UVM_ALL_ON)
        `uvm_field_int(watchdog_timeout, UVM_ALL_ON)
    `uvm_object_utils_end

    // Constraints
    constraint timeout_default_cons {
        // startup_timeout == 1000;
        watchdog_timeout == 100000000;
    }

    // Constructor
    extern function new(string name="uvmt_fifo_test_cfg");

endclass : uvmt_fifo_test_cfg_c


function uvmt_fifo_test_cfg_c::new(string name="uvmt_fifo_test_cfg");

    super.new(name);

endfunction : new

`endif // __UVMT_FIFO_TEST_CFG_SVH__