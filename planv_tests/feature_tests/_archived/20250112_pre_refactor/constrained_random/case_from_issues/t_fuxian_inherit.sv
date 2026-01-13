// Test if deep inheritance causes randomize() bug
// Mimicking UVM's uvm_object -> uvm_component -> uvm_test hierarchy
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
      $display("Randomize: success=%0d, value=%0d", success, value);
   endfunction
endclass


module t_fuxian_inherit;

   initial begin
      my_test_c test;

      $display("\n========================================");
      $display("Test: Inheritance Impact on randomize()");
      $display("========================================\n");

      test = new("my_test");
      test.do_randomize();

      $display("\n========================================");
      if (test.value > 10 && test.value < 20) begin
         $display("*** PASS *** value=%0d (range 11-19)", test.value);
         $display("Constraint solver called correctly");
      end else begin
         $display("*** FAIL *** value=%0d (should be 11-19)", test.value);
         $display("Wrong randomize() called!");
      end
      $display("========================================\n");

      $finish;
   end

endmodule
/* verilator lint_on WIDTHTRUNC */
