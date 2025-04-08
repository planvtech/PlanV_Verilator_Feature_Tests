// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMT_FIFO_TEST_CASE1_SVH__
`define __UVMT_FIFO_TEST_CASE1_SVH__


class uvmt_fifo_test_case1_c extends uvmt_fifo_base_test_c;

    `uvm_component_utils(uvmt_fifo_test_case1_c)

    // Constructor
    extern function new(string name="uvmt_fifo_test_case1", uvm_component parent=null);

endclass: uvmt_fifo_test_case1_c


function uvmt_fifo_test_case1_c::new(string name="uvmt_fifo_test_case1", uvm_component parent=null);
    super.new(name, parent);
endfunction

`endif // __UVMT_FIFO_TEST_CASE1_SVH__
