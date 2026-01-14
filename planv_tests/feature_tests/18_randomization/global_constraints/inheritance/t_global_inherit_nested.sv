// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: global constraints with nested inheritance

`include "test_utils.svh"

module t_global_inherit_nested;
   // Base class
   class Base;
      rand int base_var;
      constraint base_c {
         base_var inside {[1:50]};
      }
   endclass

   // Derived class extends Base
   class Derived extends Base;
      rand int derived_var;
      constraint derived_c {
         derived_var inside {[20:200]};
         base_var > derived_var;
      }
   endclass

   class Unrelated;
      rand Derived c_1;
      constraint unrelated_c {
         c_1.derived_var inside {[0:25]};
      }
      function new();
         c_1 = new();
      endfunction
   endclass

   class Unrelated2;
      rand Unrelated c_2;
      constraint unrelated2_c {
         c_2.c_1.derived_var inside {[21:23]};
      }
      function new();
         c_2 = new();
      endfunction
   endclass

   initial begin
      Unrelated2 obj = new();
      /* verilator lint_off WIDTHTRUNC */
      if (obj.randomize()) begin
         `DBG(("Base var: %0d, Derived var: %0d", obj.c_2.c_1.base_var, obj.c_2.c_1.derived_var))
      end
      /* verilator lint_off WIDTHTRUNC */
      `TEST_PASS
   end
endmodule
