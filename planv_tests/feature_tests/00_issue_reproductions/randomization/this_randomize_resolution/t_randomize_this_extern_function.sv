// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: this.randomize() resolution in extern functions

`include "test_utils.svh"

/* verilator lint_off WIDTHTRUNC */


// Test 2: Virtual base class
virtual class base_component_c;
   rand bit [7:0] base_value;

   constraint base_con {
      base_value < 100;
   }

   function new();
   endfunction
endclass

// Test 2: uvm_component-like class with randomize
class test_component_c extends base_component_c;
   rand bit [7:0] value;
   string name;
   int success;  // Added to match UVM pattern

   constraint value_con {
      value > 10;
      value < 20;
   }

   function new(string n = "test");
      name = n;
   endfunction

   // USING EXTERN PATTERN LIKE UVM!
   extern function void test_randomize();
endclass

// Implementation outside class (UVM extern pattern)
function void test_component_c::test_randomize();
   // THIS IS THE EXACT PATTERN FROM UVM TEST LINE 98!
   success = this.randomize();
   `DBG(("First randomize: success=%0d, value=%0d", success, value))

   // THIS IS THE EXACT PATTERN FROM UVM TEST LINE 102!
   if (!this.randomize()) begin
      `DBG(("ERROR: Randomization failed!"))
   end else begin
      `DBG(("INFO: Randomization succeeded, value=%0d", value))
   end
endfunction


module t_randomize_this_extern_function;

   initial begin
      test_component_c comp;
      int success_count = 0;
      int fail_count = 0;

      `DBG(("\n"))
      `DBG(("========================================"))
      `DBG(("Verilator randomize() Bug Reproduction"))
      `DBG(("========================================"))

      // Test 2: Component-like class
      `DBG(("\n=== Test 2: Component Class ==="))
      comp = new("my_component");
      comp.test_randomize();
      if (comp.value > 10 && comp.value < 20) begin
         `DBG(("PASS: Constraint applied correctly"))
         success_count++;
      end else begin
         `DBG(("FAIL: Constraint NOT applied! value=%0d (should be 11-19)", comp.value))
         fail_count++;
      end

      // Summary
      `DBG(("\n"))
      `DBG(("========================================"))
      `DBG(("Test Summary"))
      `DBG(("========================================"))
      `DBG(("PASS: %0d tests", success_count))
      `DBG(("FAIL: %0d tests", fail_count))

      if (fail_count == 0) begin
         `DBG(("\n*** TEST PASSED ***"))
      end else begin
         `DBG(("\n*** TEST FAILED ***"))
         `DBG(("Verilator randomize() issue reproduced!"))
      end
      `DBG(("========================================\n"))

      `TEST_PASS
   end

endmodule
/* verilator lint_off WIDTHTRUNC */