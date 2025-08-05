// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class Cfg;
  bit [7:0] max_limit;
  bit [7:0] min_limit;
endclass

class Payload;
  rand bit [7:0] data;
  Cfg cfg;

  function new();
    cfg = new();
    cfg.max_limit = 50;
    cfg.min_limit = 49;
    data = 0;
  endfunction

  constraint c_data {
    cfg.min_limit < data;
  }
endclass

module t_randomize_with_classMember;
  Payload p = new();
  bit success;

  initial begin
    success = p.randomize() with { data <= cfg.max_limit; };
    if (!success) $stop;
    $display("p.data = %0d, cfg.min_limit = %0d, cfg.max_limit = %0d", p.data, p.cfg.min_limit, p.cfg.max_limit);
    if (!(p.data > p.cfg.min_limit && p.data <= p.cfg.max_limit)) $stop;

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
