// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: unique constraint stress testing with large arrays

`include "test_utils.svh"

class StressTest200;
  rand bit [15:0] arr[200];

  constraint unique_c {
    unique {arr};
  }

  function bit check();
    int duplicate_count = 0;
    for (int i = 0; i < 200; i++) begin
      for (int j = i + 1; j < 200; j++) begin
        if (arr[i] == arr[j]) duplicate_count++;
      end
    end
    if (duplicate_count > 0) begin
      $error("StressTest200: Found %0d duplicates", duplicate_count);
      return 0;
    end
    `DBG(("StressTest200: PASSED - 200 unique values"))
    return 1;
  endfunction
endclass

class StressTest256;
  rand bit [15:0] arr[256];

  constraint unique_c {
    unique {arr};
  }

  function bit check();
    int duplicate_count = 0;
    for (int i = 0; i < 256; i++) begin
      for (int j = i + 1; j < 256; j++) begin
        if (arr[i] == arr[j]) duplicate_count++;
      end
    end
    if (duplicate_count > 0) begin
      $error("StressTest256: Found %0d duplicates", duplicate_count);
      return 0;
    end
    `DBG(("StressTest256: PASSED - 256 unique values"))
    return 1;
  endfunction
endclass

// Test with narrow bit width (should hit limits faster)
class NarrowWidth;
  rand bit [7:0] arr[256];  // 256 elements with 8-bit width = exactly fills space

  constraint unique_c {
    unique {arr};
  }

  function bit check();
    bit [7:0] seen[256];
    int count = 0;

    for (int i = 0; i < 256; i++) begin
      seen[i] = 0;
    end

    for (int i = 0; i < 256; i++) begin
      if (seen[arr[i]] != 0) begin
        $error("NarrowWidth: Duplicate value 0x%h at index %0d", arr[i], i);
        return 0;
      end
      seen[arr[i]] = 1;
      count++;
    end

    if (count != 256) begin
      $error("NarrowWidth: Only %0d unique values, expected 256", count);
      return 0;
    end

    `DBG(("NarrowWidth: PASSED - All 256 possible values used exactly once"))
    return 1;
  endfunction
endclass

// Test impossible case: more elements than possible values
class ImpossibleNarrow;
  rand bit [7:0] arr[257];  // 257 elements but only 256 possible values

  constraint unique_c {
    unique {arr};
  }
endclass

module t_constraint_unique_stress;
  initial begin
    StressTest200 t200;
    StressTest256 t256;
    NarrowWidth tn;
    ImpossibleNarrow timp;
    automatic int success = 0;
    longint start_time, end_time;

    `DBG(("=== Stress Test 200 Elements ==="))
    t200 = new();
    start_time = $time;
    /* verilator lint_off WIDTHTRUNC */
    if (t200.randomize()) begin
    /* verilator lint_on WIDTHTRUNC */
      end_time = $time;
      `DBG(("Randomization time: %0d ns", end_time - start_time))
      if (t200.check()) success++;
    end else begin
      $error("Stress Test 200: Randomization failed");
    end

    `DBG(("\n=== Stress Test 256 Elements ==="))
    t256 = new();
    start_time = $time;
    /* verilator lint_off WIDTHTRUNC */
    if (t256.randomize()) begin
    /* verilator lint_on WIDTHTRUNC */
      end_time = $time;
      `DBG(("Randomization time: %0d ns", end_time - start_time))
      if (t256.check()) success++;
    end else begin
      $error("Stress Test 256: Randomization failed");
    end

    `DBG(("\n=== Narrow Width Test (256 elements, 8-bit) ==="))
    tn = new();
    start_time = $time;
    /* verilator lint_off WIDTHTRUNC */
    if (tn.randomize()) begin
    /* verilator lint_on WIDTHTRUNC */
      end_time = $time;
      `DBG(("Randomization time: %0d ns", end_time - start_time))
      if (tn.check()) success++;
    end else begin
      $error("Narrow Width Test: Randomization failed");
    end

    `DBG(("\n=== Impossible Narrow Test (257 elements, 8-bit) ==="))
    timp = new();
    /* verilator lint_off WIDTHTRUNC */
    if (timp.randomize()) begin
    /* verilator lint_on WIDTHTRUNC */
      $error("Impossible test should have failed!");
    end else begin
      `DBG(("Impossible Narrow: PASSED - correctly failed"))
      success++;
    end

    `DBG(("\n=== SUMMARY ==="))
    `DBG(("Tests passed: %0d/4", success))
    if (success == 4) begin
      `TEST_PASS
    end else begin
      $fatal(1, "Some tests failed");
    end
  end
endmodule
