// Test with actual UVM base classes to reproduce bug
// Hypothesis: Inheriting from uvm_test/uvm_component causes the issue
/* verilator lint_off WIDTHTRUNC */

`include "uvm_macros.svh"

package test_uvm_pkg;
   import uvm_pkg::*;

   // Minimal test inheriting from uvm_test (like UVM base_test)
   class my_test_c extends uvm_test;
      rand bit [7:0] value;
      int success;

      constraint value_con {
         value > 10;
         value < 20;
      }

      `uvm_component_utils(my_test_c)

      function new(string name = "my_test", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      // Replicate UVM build_phase pattern
      virtual function void build_phase(uvm_phase phase);
         super.build_phase(phase);

         // THIS IS THE PATTERN FROM UVM TEST
         success = this.randomize();
         $display("Randomize in build_phase: success=%0d, value=%0d", success, value);

         if (value > 10 && value < 20) begin
            `uvm_info("TEST", $sformatf("PASS: value=%0d in range 11-19", value), UVM_LOW)
         end else begin
            `uvm_error("TEST", $sformatf("FAIL: value=%0d NOT in range 11-19", value))
         end
      endfunction

   endclass

endpackage : test_uvm_pkg


module t_fuxian_uvm;
   import uvm_pkg::*;
   import test_uvm_pkg::*;

   initial begin
      run_test("my_test_c");
   end

endmodule
/* verilator lint_on WIDTHTRUNC */
