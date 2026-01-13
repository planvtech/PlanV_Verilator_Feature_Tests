// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


class CfgBase;
  bit [7:0] limit = 50;
endclass

class Pkg extends CfgBase;
  rand bit [7:0] val;

  function bit test();
    return randomize() with { val <= limit; val > 49; };
  endfunction
endclass

module t_randomize_membersel_fixed3;
  Pkg p = new();

  initial begin
    if (!p.test()) $stop;
    $display("val = %0d, limit = %0d", p.val, p.limit);
    if (p.val > p.limit) $stop;

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
