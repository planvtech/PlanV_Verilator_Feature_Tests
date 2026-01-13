// DESCRIPTION: Verilator: Test unique constraint variable naming and scoping
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

// Test arrays with similar names to check for naming conflicts in SMT generation

class SimilarNames;
  rand bit [7:0] arr[4];
  rand bit [7:0] arr_1[4];
  rand bit [7:0] arr_2[4];
  rand bit [7:0] arr_copy[4];

  constraint unique_arr {
    unique {arr};
  }

  constraint unique_arr_1 {
    unique {arr_1};
  }

  constraint unique_arr_2 {
    unique {arr_2};
  }

  constraint unique_arr_copy {
    unique {arr_copy};
  }

  function bit check();
    bit pass = 1;

    // Check arr
    for (int i = 0; i < 4; i++) begin
      for (int j = i + 1; j < 4; j++) begin
        if (arr[i] == arr[j]) begin
          $error("arr[%0d] == arr[%0d]", i, j);
          pass = 0;
        end
      end
    end

    // Check arr_1
    for (int i = 0; i < 4; i++) begin
      for (int j = i + 1; j < 4; j++) begin
        if (arr_1[i] == arr_1[j]) begin
          $error("arr_1[%0d] == arr_1[%0d]", i, j);
          pass = 0;
        end
      end
    end

    // Check arr_2
    for (int i = 0; i < 4; i++) begin
      for (int j = i + 1; j < 4; j++) begin
        if (arr_2[i] == arr_2[j]) begin
          $error("arr_2[%0d] == arr_2[%0d]", i, j);
          pass = 0;
        end
      end
    end

    // Check arr_copy
    for (int i = 0; i < 4; i++) begin
      for (int j = i + 1; j < 4; j++) begin
        if (arr_copy[i] == arr_copy[j]) begin
          $error("arr_copy[%0d] == arr_copy[%0d]", i, j);
          pass = 0;
        end
      end
    end

    if (pass) $display("SimilarNames: PASSED");
    return pass;
  endfunction
endclass

// Test nested classes with same array names
class Outer;
  rand bit [7:0] data[3];

  constraint unique_data {
    unique {data};
  }

  function bit check();
    for (int i = 0; i < 3; i++) begin
      for (int j = i + 1; j < 3; j++) begin
        if (data[i] == data[j]) begin
          $error("Outer::data[%0d] == data[%0d]", i, j);
          return 0;
        end
      end
    end
    $display("Outer: PASSED");
    return 1;
  endfunction
endclass

class Inner;
  rand bit [7:0] data[3];  // Same name as in Outer

  constraint unique_data {
    unique {data};
  }

  function bit check();
    for (int i = 0; i < 3; i++) begin
      for (int j = i + 1; j < 3; j++) begin
        if (data[i] == data[j]) begin
          $error("Inner::data[%0d] == data[%0d]", i, j);
          return 0;
        end
      end
    end
    $display("Inner: PASSED");
    return 1;
  endfunction
endclass

// Test multiple randomizations of same object
class MultipleRandomize;
  rand bit [15:0] values[5];

  constraint unique_c {
    unique {values};
  }

  function bit check(int iteration);
    bit [15:0] seen[16'hFFFF];

    for (int i = 0; i < 16'hFFFF; i++) seen[i] = 0;

    for (int i = 0; i < 5; i++) begin
      if (seen[values[i]] != 0) begin
        $error("Iteration %0d: Duplicate value 0x%h", iteration, values[i]);
        return 0;
      end
      seen[values[i]] = 1;
    end

    $display("Iteration %0d: PASSED - values: %p", iteration, values);
    return 1;
  endfunction
endclass

module t_constraint_unique_naming;
  initial begin
    SimilarNames sn;
    Outer outer;
    Inner inner;
    MultipleRandomize mr;
    automatic int success = 0;

    /* verilator lint_off WIDTHTRUNC */
    $display("=== Test 1: Similar Array Names ===");
    sn = new();
    if (sn.randomize()) begin
      if (sn.check()) success++;
    end else begin
      $fatal(1, "SimilarNames randomization failed");
    end

    $display("\n=== Test 2: Outer Class ===");
    outer = new();
    if (outer.randomize()) begin
      if (outer.check()) success++;
    end else begin
      $fatal(1, "Outer randomization failed");
    end

    $display("\n=== Test 3: Inner Class (same member name) ===");
    inner = new();
    if (inner.randomize()) begin
      if (inner.check()) success++;
    end else begin
      $fatal(1, "Inner randomization failed");
    end

    $display("\n=== Test 4: Multiple Randomizations ===");
    mr = new();
    for (int i = 0; i < 5; i++) begin
      if (!mr.randomize()) begin
        $fatal(1, "Multiple randomization %0d failed", i);
      end
      if (!mr.check(i)) begin
        $fatal(1, "Multiple randomization %0d check failed", i);
      end
    end
    success++;

    $display("\n=== SUMMARY ===");
    $display("Tests passed: %0d/4", success);
    if (success == 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $fatal(1, "Some tests failed");
    end
    /* verilator lint_on WIDTHTRUNC */
  end
endmodule
