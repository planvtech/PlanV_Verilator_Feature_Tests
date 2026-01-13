// Simplified test to reproduce Verilator randomize() bug
// Root cause: When class is in package, first=false, falls back to std::randomize
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
      $display("Randomize result: success=%0d, value=%0d", success, value);

      if (value > 10 && value < 20) begin
         $display("PASS: Constraint applied (value=%0d in range 11-19)", value);
      end else begin
         $display("FAIL: Constraint NOT applied (value=%0d should be 11-19)", value);
      end
   endfunction

endpackage : test_pkg


module t_fuxian_pkg;

   import test_pkg::*;

   initial begin
      test_c obj;

      $display("\n========================================");
      $display("Bug Reproduction: Package Scope Issue");
      $display("========================================\n");

      obj = new();
      obj.do_test();

      $display("\n========================================");
      if (obj.value > 10 && obj.value < 20) begin
         $display("*** TEST PASSED ***");
         $display("Bug NOT reproduced (randomize worked)");
      end else begin
         $display("*** TEST FAILED ***");
         $display("Bug REPRODUCED (randomize stub called)");
      end
      $display("========================================\n");

      $finish;
   end

endmodule
/* verilator lint_on WIDTHTRUNC */
