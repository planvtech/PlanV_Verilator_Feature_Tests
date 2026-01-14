// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: scheduler inactive region with virtual interfaces

`include "test_utils.svh"

interface If;
  logic [31:0] inc;
endinterface

module t_vif_sched_inactive;

  logic clk = 0;
  logic [31:0] inc1 = 0;
  logic [31:0] inc2 = 0;
  int cyc = 0;

  If intf1();
  If intf2();
  virtual If vif1 = intf1;
  virtual If vif2 = intf2;

  // assign vif1.inc  = inc1;
  always @(posedge clk) begin
    vif1.inc <= inc1;
  end
  assign intf2.inc = inc2;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc >= 10) begin
      `TEST_PASS
    end
  end

  always @(intf1.inc) begin
    `DBG(("[%0t] intf1.inc==%h", $time, intf1.inc))
  end
  always @(vif2.inc) begin
    `DBG(("[%0t] vif2.inc==%h", $time, vif2.inc))
  end

  initial begin
    repeat (30) #5ns clk = ~clk;
  end

  initial begin
    inc1 = 1;
    inc2 = 1;

    repeat (8) begin
      #10ns;
      inc1 = inc1 + 1;
      inc2 = inc2 + 1;
    end

  end

endmodule
