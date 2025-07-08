// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class Cfg;
  bit [7:0] limit;
endclass

class Payload;
  rand bit [7:0] data;
  Cfg cfg;

  function new();
    cfg = new();
    cfg.limit = 50; // Default limit
    data = 0; // Initialize data
  endfunction
endclass

module t_randomize_with_classMember;
  Payload p = new();
  bit success;

  initial begin
    success = p.randomize() with { data <= cfg.limit; };
    if (!success) $stop;
    $display("p.data = %0d, cfg.limit = %0d", p.data, p.cfg.limit);
    if (p.data > p.cfg.limit) $stop;

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
