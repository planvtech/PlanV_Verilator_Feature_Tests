// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: rand_mode() behavior with member-selected variables
//
// Test for GitHub Issue #6740: Regression in constraints with rand_mode
// FIXED IN: PR #6797 (merged 2025-12-11)
// REFERENCE: https://github.com/verilator/verilator/issues/6740

`include "test_utils.svh"

class RandomValue;
  rand int value;
  constraint small_int_c { value < 10; }

  task disable_val();
    value.rand_mode(0);
  endtask
endclass

class Base;
  rand RandomValue v = new;
endclass

class Foo extends Base;
endclass

module t_issue_6740;
  initial begin
    Foo d = new;
    Base b = d;

    // Disable randomization of v.value
    b.v.disable_val();

    // Set value to 11 (violates constraint, but should be OK since rand_mode is off)
    b.v.value = 11;

    // Randomize should fail because value is set to 11 and can't be changed
    if (bit'(b.randomize())) begin
      `DBG(("ERROR: randomize() should have failed"))
      $stop;
    end

    // Value should remain 11
    if (b.v.value != 11) begin
      `DBG(("ERROR: value changed from 11 to %0d", b.v.value))
      $stop;
    end

    `TEST_PASS
  end
endmodule
