// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: this.randomize() resolution in deep inheritance hierarchies

`include "test_utils.svh"

/* verilator lint_off WIDTHTRUNC */

// Base class (like uvm_object)
virtual class base_object_c;
   function new();
   endfunction

   virtual function int randomize();
      return 1;  // Default implementation
   endfunction
endclass

// Component class (like uvm_component)
virtual class component_c extends base_object_c;
   string name;

   function new(string n = "component");
      super.new();
      name = n;
   endfunction
endclass

// Test class (like uvm_test)
class my_test_c extends component_c;
   rand bit [7:0] value;
   int success;

   constraint value_con {
      value > 10;
      value < 20;
   }

   function new(string n = "test");
      super.new(n);
   endfunction

   // Method that calls randomize (like build_phase)
   function void do_randomize();
      // KEY: Does this.randomize() resolve to:
      // 1. my_test_c::randomize (constraint solver) - CORRECT
      // 2. base_object_c::randomize (virtual function returning 1) - WRONG
      // 3. std::randomize - WRONG
      success = this.randomize();
      `DBG(("Randomize: success=%0d, value=%0d", success, value))
   endfunction
endclass


module t_randomize_this_deep_inheritance;

   initial begin
      my_test_c test;

      `DBG(("\n========================================"))
      `DBG(("Test: Inheritance Impact on randomize()"))
      `DBG(("========================================\n"))

      test = new("my_test");
      test.do_randomize();

      `DBG(("\n========================================"))
      if (test.value > 10 && test.value < 20) begin
         `DBG(("*** PASS *** value=%0d (range 11-19)", test.value))
         `DBG(("Constraint solver called correctly"))
      end else begin
         `DBG(("*** FAIL *** value=%0d (should be 11-19)", test.value))
         `DBG(("Wrong randomize() called!"))
      end
      `DBG(("========================================\n"))

      `TEST_PASS
   end

endmodule
/* verilator lint_on WIDTHTRUNC */
