// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


interface INTF;
  logic a;
  logic b;
endinterface

module t_interface_passed;
  logic val;
  INTF intf1(); 
  virtual INTF vif1 = intf1;

  assign intf1.a = val;

  initial begin
    val = 0;
    #1ns;
    if(vif1.a !== 0) begin
      $display("FAIL: vif1.a should be 0, but is %0d", vif1.a);
      $stop;
    end
    val = 1;
    #1ns;
    if(vif1.a !== 1) begin
      $display("FAIL: vif1.a should be 1, but is %0d", vif1.a);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
