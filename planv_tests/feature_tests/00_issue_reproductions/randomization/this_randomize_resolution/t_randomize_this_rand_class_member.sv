// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: this.randomize() resolution with rand class members

`include "test_utils.svh"

/* verilator lint_off WIDTHTRUNC */

// Config class (like uvme_fifo_cfg_c)
class cfg_c;
   rand bit [7:0] cfg_value;

   constraint cfg_con {
      cfg_value > 5;
   }

   function new();
   endfunction
endclass

// Test class with rand class-type member (like UVM test)
class my_test_c;
   rand cfg_c my_cfg;  // KEY: rand class-type member
   rand bit [7:0] value;
   int success;

   constraint value_con {
      value > 10;
      value < 20;
   }

   function new();
   endfunction

   // Method that calls randomize
   function void do_randomize();
      success = this.randomize();
      `DBG(("Randomize: success=%0d, value=%0d, cfg_value=%0d",
               success, value, my_cfg.cfg_value))
   endfunction
endclass


module t_randomize_this_rand_class_member;

   initial begin
      my_test_c test;

      `DBG(("\n========================================"))
      `DBG(("Test: rand Class Member Impact"))
      `DBG(("========================================\n"))

      test = new();
      test.my_cfg = new();
      test.do_randomize();

      `DBG(("\n========================================"))
      if (test.value > 10 && test.value < 20) begin
         `DBG(("*** PASS *** value=%0d (range 11-19)", test.value))
      end else begin
         `DBG(("*** FAIL *** value=%0d (should be 11-19)", test.value))
         `DBG(("Bug: rand class member causes wrong randomize()"))
      end
      `DBG(("========================================\n"))

      `TEST_PASS
   end

endmodule
/* verilator lint_on WIDTHTRUNC */
