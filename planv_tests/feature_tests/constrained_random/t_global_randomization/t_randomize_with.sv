// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech

class Payload;
  rand bit [7:0] data;
endclass

module t_randomize_with;
  Payload p = new();
  bit success;
  initial begin
    success = p.randomize() with { data inside {[100:200]}; };
    if (!success) $stop;
    $display("p.data = %0d", p.data);
    if (!(p.data inside {[100:200]})) $stop;

    // Successful execution marker
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
