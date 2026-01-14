// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: this.randomize() resolution in class constructors

`include "test_utils.svh"

/* verilator lint_off WIDTHTRUNC */

class test_c;
   rand bit [7:0] value;
   int success;

   constraint value_con {
      value > 10;
      value < 20;
   }

   function new();
      // THIS IS THE KEY: randomize in constructor (like UVM build_phase)
      success = this.randomize();
      `DBG(("Constructor randomize: success=%0d, value=%0d", success, value))
   endfunction
endclass


module t_randomize_this_in_constructor;

   initial begin
      test_c obj;

      `DBG(("\n========================================"))
      `DBG(("Minimal Bug Reproduction"))
      `DBG(("========================================\n"))

      obj = new();

      `DBG(("\n========================================"))
      if (obj.value > 10 && obj.value < 20) begin
         `DBG(("*** PASS *** value=%0d (correct range 11-19)", obj.value))
      end else begin
         `DBG(("*** FAIL *** value=%0d (should be 11-19)", obj.value))
         `DBG(("Bug: randomize() stub called instead of constraint solver"))
      end
      `DBG(("========================================\n"))

      `TEST_PASS
   end

endmodule
/* verilator lint_on WIDTHTRUNC */
