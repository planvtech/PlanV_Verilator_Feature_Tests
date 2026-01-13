package uvm_pkg;
  virtual class uvm_object;
  endclass

  class uvm_sequence_item;
  endclass

  virtual class uvm_sequencer_param_base;
    function void send_request(uvm_sequence_item t);
      uvm_sequence_item par;
      if (0 == par.randomize()) begin
      end
    endfunction
  endclass

  class uvm_reg_item extends uvm_sequence_item;
    rand uvm_object extension;
  endclass

  class uvm_reg_field extends uvm_object;
    rand int value;
    virtual function bit get_rand_mode();
      return bit'(value.rand_mode());
    endfunction
  endclass

endpackage

program t_constraint_membersel_randmode;
  import uvm_pkg::*;

  class reg_r extends uvm_object;
    rand int value;
    local rand uvm_reg_field _dummy;
    constraint _dummy_is_reg {_dummy.value == value;}
  endclass

  initial begin
    reg_r r;
    r = new;
    $finish;
  end
endprogram
