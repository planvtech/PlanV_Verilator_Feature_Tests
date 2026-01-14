// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: this.randomize() resolution in package scope

`include "test_utils.svh"

/* verilator lint_off WIDTHTRUNC */

package test_pkg;

   // Simple test class with randomize
   class test_c;
      rand bit [7:0] value;
      int success;

      constraint value_con {
         value > 10;
         value < 20;
      }

      function new();
      endfunction

      // This pattern triggers the bug
      extern function void do_test();
   endclass

   // Implementation outside class
   function void test_c::do_test();
      // BUG: this.randomize() incorrectly resolves to std::randomize
      success = this.randomize();
      `DBG(("Randomize result: success=%0d, value=%0d", success, value))

      if (value > 10 && value < 20) begin
         `DBG(("PASS: Constraint applied (value=%0d in range 11-19)", value))
      end else begin
         `DBG(("FAIL: Constraint NOT applied (value=%0d should be 11-19)", value))
      end
   endfunction

endpackage : test_pkg


module t_randomize_this_package_scope;

   import test_pkg::*;

   initial begin
      test_c obj;

      `DBG(("\n========================================"))
      `DBG(("Bug Reproduction: Package Scope Issue"))
      `DBG(("========================================\n"))

      obj = new();
      obj.do_test();

      `DBG(("\n========================================"))
      if (obj.value > 10 && obj.value < 20) begin
         `DBG(("*** TEST PASSED ***"))
         `DBG(("Bug NOT reproduced (randomize worked)"))
      end else begin
         `DBG(("*** TEST FAILED ***"))
         `DBG(("Bug REPRODUCED (randomize stub called)"))
      end
      `DBG(("========================================\n"))

      `TEST_PASS
   end

endmodule
/* verilator lint_on WIDTHTRUNC */
