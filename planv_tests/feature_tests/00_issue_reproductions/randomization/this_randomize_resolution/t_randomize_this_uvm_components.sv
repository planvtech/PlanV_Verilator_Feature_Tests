// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: this.randomize() resolution in UVM component hierarchy

`include "test_utils.svh"

/* verilator lint_off WIDTHTRUNC */

`include "uvm_macros.svh"

package test_components_pkg;
   import uvm_pkg::*;

   // Test 1: Inherit from uvm_object (not uvm_component)
   class my_object_c extends uvm_object;
      rand bit [7:0] value;
      int success;

      constraint value_con {
         value > 10;
         value < 20;
      }

      `uvm_object_utils(my_object_c)

      function new(string name = "my_object");
         super.new(name);
      endfunction

      function void do_rand();
         success = this.randomize();
         `DBG(("[OBJECT] success=%0d, value=%0d", success, value))
      endfunction
   endclass

   // Test 2: Inherit from uvm_component (base of env/agent/driver)
   class my_component_c extends uvm_component;
      rand bit [7:0] value;
      int success;

      constraint value_con {
         value > 10;
         value < 20;
      }

      `uvm_component_utils(my_component_c)

      function new(string name = "my_component", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      virtual function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         success = this.randomize();
         `DBG(("[COMPONENT] success=%0d, value=%0d", success, value))
      endfunction
   endclass

   // Test 3: Inherit from uvm_env
   class my_env_c extends uvm_env;
      rand bit [7:0] value;
      int success;

      constraint value_con {
         value > 10;
         value < 20;
      }

      `uvm_component_utils(my_env_c)

      function new(string name = "my_env", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      virtual function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         success = this.randomize();
         `DBG(("[ENV] success=%0d, value=%0d", success, value))
      endfunction
   endclass

   // Test 4: Inherit from uvm_agent
   class my_agent_c extends uvm_agent;
      rand bit [7:0] value;
      int success;

      constraint value_con {
         value > 10;
         value < 20;
      }

      `uvm_component_utils(my_agent_c)

      function new(string name = "my_agent", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      virtual function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         success = this.randomize();
         `DBG(("[AGENT] success=%0d, value=%0d", success, value))
      endfunction
   endclass

   // Test 5: Inherit from uvm_driver
   class my_driver_c extends uvm_driver#(uvm_sequence_item);
      rand bit [7:0] value;
      int success;

      constraint value_con {
         value > 10;
         value < 20;
      }

      `uvm_component_utils(my_driver_c)

      function new(string name = "my_driver", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      virtual function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         success = this.randomize();
         `DBG(("[DRIVER] success=%0d, value=%0d", success, value))
      endfunction
   endclass

   // Test 6: Inherit from uvm_test
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

      virtual function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         success = this.randomize();
         `DBG(("[TEST] success=%0d, value=%0d", success, value))
      endfunction
   endclass

endpackage : test_components_pkg


module t_randomize_this_uvm_components;
   import uvm_pkg::*;
   import test_components_pkg::*;

   initial begin
      my_object_c obj;

      `DBG(("\n========================================"))
      `DBG(("Testing Different UVM Base Classes"))
      `DBG(("========================================\n"))

      // Test standalone object (not in UVM hierarchy)
      obj = new("test_obj");
      obj.do_rand();

      if (obj.value > 10 && obj.value < 20) begin
         `DBG(("OBJECT: PASS (value=%0d)", obj.value))
      end else begin
         `DBG(("OBJECT: FAIL (value=%0d) - Bug reproduced!", obj.value))
      end

      `DBG(("\n"))

      // Run UVM test which will create component hierarchy
      run_test("my_test_c");
   end

endmodule
/* verilator lint_on WIDTHTRUNC */
