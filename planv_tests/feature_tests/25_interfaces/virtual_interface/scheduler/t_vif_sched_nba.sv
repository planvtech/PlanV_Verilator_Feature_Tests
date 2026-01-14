// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: scheduler NBA region with virtual interfaces

`include "test_utils.svh"

interface Bus1;
  logic [15:0] data;
endinterface

interface Bus2;
  logic [15:0] data;
endinterface

interface Bus3;
  logic [15:0] data;
endinterface

module t_vif_sched_nba;
  logic clk = 0;
  integer cyc = 0;
  Bus1 intf1();
  Bus2 intf2();
  Bus3 intf3();
  virtual Bus1 vif1 = intf1;
  virtual Bus2 vif2 = intf2;
  virtual Bus3 vif3 = intf3;

  logic [15:0] data;
  // assign vif2.data = data;
  always @(negedge clk) begin
    vif2.data <= data;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1)
      vif1.data = 'hdead;
    else if (cyc == 2)
      data = vif1.data;
    else if (cyc == 3)
      vif1.data = 'hbeef;
    else if (cyc == 4)
      data = vif1.data;
    else if (cyc == 5)
      intf3.data <= 'hface;
    else if (cyc == 6)
      intf3.data <= 'hcafe;
  end

  // Finish on negedge so that $finish is last
  always @(negedge clk)
    if (cyc >= 7) begin
      `TEST_PASS
    end

  always @(intf1.data) begin
    `DBG(("[%0t] intf1.data==%h", $time, intf1.data))
  end
  always @(intf2.data) begin
    `DBG(("[%0t] intf2.data==%h", $time, intf2.data))
  end
  always @(vif3.data) begin
    `DBG(("[%0t] vif3.data==%h", $time, vif3.data))
  end

  initial begin
    repeat (20) #5ns clk = ~clk;
  end
endmodule
