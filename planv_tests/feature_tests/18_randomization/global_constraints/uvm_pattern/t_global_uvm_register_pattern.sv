// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints on static class members

`include "test_utils.svh"

class uvm_reg_field;
  rand int m_value;
endclass

class reg_class;
  rand int m_value;
  rand uvm_reg_field _dummy;
  constraint _dummy_is_reg {_dummy.m_value == m_value;}
  function new();
    _dummy = new;
  endfunction
endclass

class block_class;
  rand reg_class m_r;
  function new();
    m_r = new;
  endfunction
endclass

class tb_test;
  virtual task run_phase(int phase);
    block_class regmodel;
    regmodel = new;
    // verilator lint_off IGNOREDRETURN
    void'(regmodel.randomize() with {m_r.m_value == 32'hA5;});
    // verilator lint_on IGNOREDRETURN
    if (regmodel.m_r.m_value != 32'hA5) $stop;
  endtask
endclass


// Test case 2
class axi_agent_config;
   rand bit r_ready_delays;
   constraint r_ready_delays_c {
      r_ready_delays == 0;
   }
endclass

class axi_env_config;
   rand axi_agent_config   axim_agt_cfg;
   function new();
      axim_agt_cfg = new;
   endfunction
endclass

class axi_base_test;
  axi_env_config axi_env_cfg;
  virtual function void build_phase();
    configure_axi_env();
  endfunction
  function void configure_axi_env();
    axi_env_cfg = new;
  endfunction
endclass

class axi_wrap_test extends axi_base_test;
  function void configure_axi_env();
    void'(axi_env_cfg.randomize());
  endfunction
endclass


module t_global_uvm_register_pattern;
  initial begin
    tb_test tb;
    axi_wrap_test axi_t;

    tb = new;
    tb.run_phase(0);

    axi_t = new();
    axi_t.build_phase();

    `TEST_PASS
  end
endmodule
