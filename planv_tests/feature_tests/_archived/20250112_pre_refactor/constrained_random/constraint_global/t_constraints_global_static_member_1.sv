module t_constraints_global_static_member_1;
  class uvm_reg_field;
    rand int m_value;
  endclass

  class reg_class;
    rand int m_value;
    rand uvm_reg_field _dummy;
    constraint _dummy_is_reg {_dummy.m_value == m_value;}
  endclass

  class block_class;
    rand reg_class m_r;
  endclass

  class tb_test;
    virtual task run_phase(int phase);
      block_class regmodel;
      // verilator lint_off IGNOREDRETURN
      void'(regmodel.randomize() with {m_r.m_value == 32'hA5;});
      // verilator lint_on IGNOREDRETURN
    endtask
  endclass
endmodule
