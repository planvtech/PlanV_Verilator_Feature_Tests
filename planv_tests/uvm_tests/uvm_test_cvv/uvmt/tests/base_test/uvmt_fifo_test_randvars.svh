// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMT_FIFO_TEST_RANDVARS_SVH__
`define __UVMT_FIFO_TEST_RANDVARS_SVH__


class uvmt_fifo_test_randvars_c extends uvm_object;

    rand int unsigned random_int;
    rand logic [31:0] random_logic32;
    rand logic        random_logic_bit;

    // Factory & Field
    `uvm_object_utils_begin(uvmt_fifo_test_randvars_c)
        `uvm_field_int(random_int, UVM_ALL_ON)
        `uvm_field_int(random_logic32, UVM_ALL_ON)
        `uvm_field_int(random_logic_bit, UVM_ALL_ON)
    `uvm_object_utils_end

    extern function new(string name="uvmt_fifo_test_randvars");

endclass : uvmt_fifo_test_randvars_c


function uvmt_fifo_test_randvars_c::new(string name="uvmt_fifo_test_randvars");
    
    super.new(name);

endfunction : new

`endif // __UVMT_FIFO_TEST_RANDVARS_SVH__
