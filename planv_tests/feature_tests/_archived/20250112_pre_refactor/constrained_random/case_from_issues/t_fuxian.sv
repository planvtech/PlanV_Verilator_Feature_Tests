// Test case to reproduce Verilator randomize() issue
// Issue: Verilator incorrectly generates stub functions for this.randomize()
//        instead of calling the real constraint solver
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
   $display("First randomize: success=%0d, value=%0d", success, value);

   // THIS IS THE EXACT PATTERN FROM UVM TEST LINE 102!
   if (!this.randomize()) begin
      $display("ERROR: Randomization failed!");
   end else begin
      $display("INFO: Randomization succeeded, value=%0d", value);
   end
endfunction


module t_fuxian;

   initial begin
      test_component_c comp;
      int success_count = 0;
      int fail_count = 0;

      $display("\n");
      $display("========================================");
      $display("Verilator randomize() Bug Reproduction");
      $display("========================================");

      // Test 2: Component-like class
      $display("\n=== Test 2: Component Class ===");
      comp = new("my_component");
      comp.test_randomize();
      if (comp.value > 10 && comp.value < 20) begin
         $display("PASS: Constraint applied correctly");
         success_count++;
      end else begin
         $display("FAIL: Constraint NOT applied! value=%0d (should be 11-19)", comp.value);
         fail_count++;
      end

      // Summary
      $display("\n");
      $display("========================================");
      $display("Test Summary");
      $display("========================================");
      $display("PASS: %0d tests", success_count);
      $display("FAIL: %0d tests", fail_count);

      if (fail_count == 0) begin
         $display("\n*** TEST PASSED ***");
      end else begin
         $display("\n*** TEST FAILED ***");
         $display("Verilator randomize() issue reproduced!");
      end
      $display("========================================\n");

      $finish;
   end

endmodule
/* verilator lint_off WIDTHTRUNC */