// DESCRIPTION: Verilator: Test edge cases for unique constraint
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

// Test 1: Single element array (trivially unique)
class SingleElementArray;
  rand bit [7:0] single[1];

  constraint unique_c {
    unique {single};
  }

  function void post_randomize();
    $display("SingleElementArray: single[0] = 0x%h", single[0]);
  endfunction
endclass

// Test 2: Two element array (minimal non-trivial case)
class TwoElementArray;
  rand bit [3:0] two[2];

  constraint unique_c {
    unique {two};
  }

  function void check();
    if (two[0] == two[1]) begin
      $fatal(1, "TwoElementArray: FAILED - two[0]=0x%h == two[1]=0x%h", two[0], two[1]);
    end
    $display("TwoElementArray: PASSED - two[0]=0x%h, two[1]=0x%h", two[0], two[1]);
  endfunction
endclass

// Test 3: Multiple unique arrays in same class (naming conflict test)
class MultipleUniqueArrays;
  rand bit [7:0] arr1[4];
  rand bit [7:0] arr2[4];
  rand bit [7:0] arr3[4];

  constraint unique_c1 {
    unique {arr1};
  }

  constraint unique_c2 {
    unique {arr2};
  }

  constraint unique_c3 {
    unique {arr3};
  }

  function bit check_array_unique(bit [7:0] arr[], string name);
    for (int i = 0; i < arr.size(); i++) begin
      for (int j = i + 1; j < arr.size(); j++) begin
        if (arr[i] == arr[j]) begin
          $error("%s: VIOLATION - arr[%0d] == arr[%0d] == 0x%h", name, i, j, arr[i]);
          return 0;
        end
      end
    end
    return 1;
  endfunction

  function void check();
    bit pass = 1;
    pass &= check_array_unique(arr1, "arr1");
    pass &= check_array_unique(arr2, "arr2");
    pass &= check_array_unique(arr3, "arr3");
    if (pass) $display("MultipleUniqueArrays: PASSED");
    else $fatal(1, "MultipleUniqueArrays: FAILED");
  endfunction
endclass

// Test 4: Unique with other constraints (range constraint)
class UniqueWithRange;
  rand bit [7:0] arr[5];

  constraint unique_c {
    unique {arr};
  }

  constraint range_c {
    foreach (arr[i]) {
      arr[i] inside {[10:14]};  // Only 5 valid values for 5 elements
    }
  }

  function void check();
    bit pass = 1;
    // Check uniqueness
    for (int i = 0; i < 5; i++) begin
      for (int j = i + 1; j < 5; j++) begin
        if (arr[i] == arr[j]) begin
          $error("UniqueWithRange: UNIQUENESS VIOLATION - arr[%0d] == arr[%0d] == 0x%h", i, j, arr[i]);
          pass = 0;
        end
      end
      // Check range
      if (arr[i] < 10 || arr[i] > 14) begin
        $error("UniqueWithRange: RANGE VIOLATION - arr[%0d] = 0x%h not in [10:14]", i, arr[i]);
        pass = 0;
      end
    end
    if (pass) $display("UniqueWithRange: PASSED - values: %p", arr);
    else $fatal(1, "UniqueWithRange: FAILED");
  endfunction
endclass

// Test 5: Unique with impossible constraints (should fail to randomize)
class UniqueWithImpossible;
  rand bit [7:0] arr[10];

  constraint unique_c {
    unique {arr};
  }

  constraint impossible_c {
    foreach (arr[i]) {
      arr[i] inside {[0:8]};  // Only 9 values for 10 unique elements - impossible
    }
  }
endclass

// Test 6: Larger array (performance test - 50 elements)
class LargeArray50;
  rand bit [15:0] arr50[50];

  constraint unique_c {
    unique {arr50};
  }

  function bit check();
    for (int i = 0; i < 50; i++) begin
      for (int j = i + 1; j < 50; j++) begin
        if (arr50[i] == arr50[j]) begin
          $error("LargeArray50: VIOLATION - arr50[%0d] == arr50[%0d]", i, j);
          return 0;
        end
      end
    end
    $display("LargeArray50: PASSED - 50 unique values generated");
    return 1;
  endfunction
endclass

// Test 7: Maximum reasonable size (100 elements)
class LargeArray100;
  rand bit [15:0] arr100[100];

  constraint unique_c {
    unique {arr100};
  }

  function bit check();
    for (int i = 0; i < 100; i++) begin
      for (int j = i + 1; j < 100; j++) begin
        if (arr100[i] == arr100[j]) begin
          $error("LargeArray100: VIOLATION - arr100[%0d] == arr100[%0d]", i, j);
          return 0;
        end
      end
    end
    $display("LargeArray100: PASSED - 100 unique values generated");
    return 1;
  endfunction
endclass

module t_constraint_unique_edge_cases;
  initial begin
    SingleElementArray t1;
    TwoElementArray t2;
    MultipleUniqueArrays t3;
    UniqueWithRange t4;
    UniqueWithImpossible t5;
    LargeArray50 t6;
    LargeArray100 t7;
    automatic int success_count = 0;

    /* verilator lint_off WIDTHTRUNC */
    $display("=== Test 1: Single Element Array ===");
    t1 = new();
    if (t1.randomize()) begin
      t1.post_randomize();
      success_count++;
    end else begin
      $fatal(1, "Test 1 randomization failed");
    end

    $display("\n=== Test 2: Two Element Array ===");
    t2 = new();
    if (t2.randomize()) begin
      t2.check();
      success_count++;
    end else begin
      $fatal(1, "Test 2 randomization failed");
    end

    $display("\n=== Test 3: Multiple Unique Arrays ===");
    t3 = new();
    if (t3.randomize()) begin
      t3.check();
      success_count++;
    end else begin
      $fatal(1, "Test 3 randomization failed");
    end

    $display("\n=== Test 4: Unique With Range Constraint ===");
    t4 = new();
    if (t4.randomize()) begin
      t4.check();
      success_count++;
    end else begin
      $fatal(1, "Test 4 randomization failed");
    end

    $display("\n=== Test 5: Unique With Impossible Constraint ===");
    t5 = new();
    if (t5.randomize()) begin
      $fatal(1, "Test 5 should have failed but succeeded!");
    end else begin
      $display("Test 5: PASSED - correctly failed on impossible constraints");
      success_count++;
    end

    $display("\n=== Test 6: Large Array (50 elements) ===");
    t6 = new();
    if (t6.randomize()) begin
      if (t6.check()) success_count++;
      else $fatal(1, "Test 6 check failed");
    end else begin
      $fatal(1, "Test 6 randomization failed");
    end

    $display("\n=== Test 7: Large Array (100 elements) ===");
    t7 = new();
    if (t7.randomize()) begin
      if (t7.check()) success_count++;
      else $fatal(1, "Test 7 check failed");
    end else begin
      $fatal(1, "Test 7 randomization failed");
    end

    $display("\n=== SUMMARY ===");
    $display("Tests passed: %0d/7", success_count);
    if (success_count == 7) begin
      $display("*** ALL TESTS PASSED ***");
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $fatal(1, "*** SOME TESTS FAILED ***");
    end
    /* verilator lint_on WIDTHTRUNC */
  end
endmodule
