// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: unsatisfiable constraint detection and handling

`include "test_utils.svh"

class Packet;
  rand bit [7:0] addr;
  rand bit [7:0] data;

  constraint addr_range { addr < 127; }
  constraint data_range { data > 10 && data < 200; }

  function void check(bit [7:0] a, bit [7:0] d);
    // Use randomize() with to force specific values that may conflict with class constraints
    if (!randomize() with { addr == a; data == d; }) begin
      `DBG(("Randomization failed for addr=%0d, data=%0d", a, d))
    end else begin
      `DBG(("Randomization succeeded for addr=%0d, data=%0d -> addr=%0d, data=%0d",
               a, d, addr, data))
    end
  endfunction
endclass

class TestConflict;
  rand bit [7:0] x;

  constraint c1 { x > 100; }
  constraint c2 { x < 50; }

  function bit try_randomize();
    return randomize();
  endfunction
endclass

class TestQuoteInConstraint;
  rand bit [7:0] value;

  // Test constraint with string literal containing quotes
  constraint valid_range {
    value > 10 && value < 200;  // This is "valid" range
  }
endclass

module t_constraint_unsat_basic;
  initial begin
    Packet pkt;
    TestConflict tc;
    TestQuoteInConstraint tq;

    pkt = new;

    // Test 1: Valid randomization - should succeed
    `DBG(("\n=== Test 1: Valid constraints ==="))
    pkt.check(50, 100);

    // Test 2: addr out of range - should fail and report addr_range constraint
    `DBG(("\n=== Test 2: addr out of range ==="))
    pkt.check(128, 18);

    // Test 3: data out of range (too small) - should fail and report data_range constraint
    `DBG(("\n=== Test 3: data out of range (too small) ==="))
    pkt.check(100, 5);

    // Test 4: data out of range (too large) - should fail and report data_range constraint
    `DBG(("\n=== Test 4: data out of range (too large) ==="))
    pkt.check(100, 250);

    // Test 5: Both constraints violated - should report both
    `DBG(("\n=== Test 5: Both constraints violated ==="))
    pkt.check(200, 5);

    // Test 6: Conflicting constraints - should fail
    `DBG(("\n=== Test 6: Conflicting constraints (x > 100 && x < 50) ==="))
    tc = new;
    if (!tc.try_randomize()) begin
      `DBG(("Expected failure: conflicting constraints detected"))
    end else begin
      `DBG(("ERROR: Should have failed with conflicting constraints"))
      $stop;
    end

    // Test 7: Test quote handling in constraint source
    `DBG(("\n=== Test 7: Constraint with quotes in comment ==="))
    tq = new;
    if (tq.randomize()) begin
      `DBG(("Quote test passed, value=%0d", tq.value))
    end

    `TEST_PASS
  end
endmodule
