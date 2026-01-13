// Minimal reproduction of Verilator randomize() bug
// Based on UVM pattern: randomize called in constructor
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
      $display("Constructor randomize: success=%0d, value=%0d", success, value);
   endfunction
endclass


module t_fuxian_simple;

   initial begin
      test_c obj;

      $display("\n========================================");
      $display("Minimal Bug Reproduction");
      $display("========================================\n");

      obj = new();

      $display("\n========================================");
      if (obj.value > 10 && obj.value < 20) begin
         $display("*** PASS *** value=%0d (correct range 11-19)", obj.value);
      end else begin
         $display("*** FAIL *** value=%0d (should be 11-19)", obj.value);
         $display("Bug: randomize() stub called instead of constraint solver");
      end
      $display("========================================\n");

      $finish;
   end

endmodule
/* verilator lint_on WIDTHTRUNC */
