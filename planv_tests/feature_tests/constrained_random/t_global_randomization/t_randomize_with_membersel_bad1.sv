// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class Cfg;
  bit [7:0] limit = 120;
endclass

class Payload;
  rand bit [7:0] data;
  Cfg cfg = new();

  function bit run();
    return randomize() with { data <= cfg.limit; };
  endfunction
endclass

module t_randomize_with_membersel_bad1;
  Payload p = new();
  bit success;

  initial begin
    success = p.run();
    if (!success) $stop;
    $display("data = %0d, limit = %0d", p.data, p.cfg.limit);
    if (p.data > p.cfg.limit) $stop;

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
