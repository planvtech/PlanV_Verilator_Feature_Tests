// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


interface Bus;
  logic [15:0] data;
endinterface

module t_interface_t1;
  Bus intf1(), intf2();
  virtual Bus vif1 = intf1, vif2 = intf2;

  task assign_to_vif2();
    if (0) return;
    #1 vif2.data = 'hfafa; #1;
  endtask

  initial forever begin
    intf1.data = 'hdead;
    if (1) begin
      #1 vif2.data = 'hbeef; #1;
    end
    intf1.data = 'hcafe;
    if (0); else begin
      #1 vif2.data = 'hface; #1;
    end
    intf1.data = 'hfeed;
    while ($time < 5) begin
      #1 vif2.data = 'hdeed; #1;
    end
    intf1.data = 'hdeaf;
    assign_to_vif2;
    intf1.data = 'hbebe;

    #1 $write("*-* All Finished *-*\n");
    $finish;
  end

  always_comb if ($time < 9) $write("[%0d] vif1.data==%h\n", $time, vif1.data);
  always_comb if ($time < 9) $write("[%0d] intf1.data==%h\n", $time, intf1.data);
  always_comb if ($time < 9) $write("[%0d] vif2.data==%h\n", $time, vif2.data);
  always_comb if ($time < 9) $write("[%0d] intf2.data==%h\n", $time, intf2.data);

endmodule

