// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: virtual interface passing between functions

`include "test_utils.svh"

interface INTF;
  logic a;
  logic b;
endinterface

module t_vif_basic_passing;
  logic val;
  INTF intf1(); 
  virtual INTF vif1 = intf1;

  assign intf1.a = val;

  initial begin
    val = 0;
    #1ns;
    if(vif1.a !== 0) begin
      `DBG(("FAIL: vif1.a should be 0, but is %0d", vif1.a))
      $stop;
    end
    val = 1;
    #1ns;
    if(vif1.a !== 1) begin
      `DBG(("FAIL: vif1.a should be 1, but is %0d", vif1.a))
      $stop;
    end
    `TEST_PASS
  end

endmodule
