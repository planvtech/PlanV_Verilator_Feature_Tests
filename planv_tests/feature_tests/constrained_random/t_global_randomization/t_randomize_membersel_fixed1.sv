// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class Payload;
  rand bit [7:0] data;
  rand bit [7:0] limit_min;
  bit [7:0] limit_max = 140;

  function bit run();
    return randomize() with { 
      data inside {[100:200]};
      limit_min inside {[110:120]};
      data <= limit_max;
      data >= limit_min; };
  endfunction   
endclass

module t_randomize_membersel_fixed1;
  Payload p = new();
  bit success, valid;
  initial begin
    success = p.run();
    valid = success && (p.data inside {[100:200]}) && (p.limit_min inside {[110:120]}) && (p.limit_max == 140) && (p.data <= p.limit_max) && (p.data >= p.limit_min);
    
    $display("p.data = %0d, p.limit_min = %0d, p.limit_max = %0d", p.data, p.limit_min, p.limit_max);
    if (!valid) $stop;
    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

