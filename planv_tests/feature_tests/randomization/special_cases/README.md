# Special Cases

Tests for special scenarios, edge cases, and issue reproductions that don't fit neatly into the IEEE 1800-2023 chapter structure.

## Subdirectories

### issue_reproductions/
Reproduction cases for reported bugs and GitHub issues.

**Purpose**: Each test reproduces a specific issue to verify bug fixes and prevent regressions.

**Naming Convention**: `t_issue_<identifier>_<brief_description>.sv`

Examples:
- `t_issue_fuxian_randomize_basic.sv` - Fuxian's basic randomize bug
- `t_issue_1800.sv` - GitHub issue #1800 reproduction
- `t_issue_6740.sv` - GitHub issue #6740 reproduction

**Test Requirements**:
1. **Header comment** must describe the issue:
   ```systemverilog
   // DESCRIPTION: Reproduction of GitHub issue #1234
   //
   // Issue: randomize() fails when using nested classes with...
   // Expected: Should randomize successfully
   // Actual (before fix): Solver error / crash / wrong values
   ```

2. **Reference** to the original issue:
   ```systemverilog
   // See: https://github.com/verilator/verilator/issues/1234
   ```

3. **Minimal reproducer**: Test should be as simple as possible while still triggering the bug

4. **Clear success criteria**: Test must clearly pass when bug is fixed

**Lifecycle**:
- Tests are added when bugs are reported
- Tests initially fail (reproduce the bug)
- After fix, tests pass
- Tests remain to prevent regression

### edge_cases/
Edge cases, corner scenarios, and boundary condition tests.

**Purpose**: Tests that explore unusual but valid SystemVerilog constructs or boundary conditions.

Examples of edge cases:
- Unsatisfiable constraints (should return 0)
- Empty arrays in constraints
- Maximum/minimum value boundaries
- Extreme nesting depths
- Unusual but legal syntax combinations
- Solver edge cases (e.g., very large constraint sets)

**Naming Convention**: `t_<feature>_edge_<scenario>.sv`

Examples:
- `t_constraint_unsatisfiable.sv` - Constraints that cannot be satisfied
- `t_constraint_array_empty.sv` - Constraints on empty arrays
- `t_constraint_maxint.sv` - Constraints at integer boundaries
- `t_randomize_nested_depth.sv` - Deeply nested class randomization

**Test Requirements**:
1. **Describe the edge case** in comments
2. **Specify expected behavior** (should pass/fail/warn)
3. **Reference IEEE spec** if applicable

Example:
```systemverilog
// DESCRIPTION: Edge case - unsatisfiable constraints
//
// Tests that randomize() correctly returns 0 when constraints
// cannot be satisfied.
//
// IEEE 1800-2023 §18.6: randomize() returns 0 if constraints
// are unsatisfiable.

class Test;
  rand bit [2:0] x;
  constraint c {
    x > 10;  // Impossible for 3-bit value
  }
endclass

module t_constraint_unsatisfiable;
  initial begin
    Test t = new;
    if (t.randomize()) begin
      $display("ERROR: Should have failed!");
      $stop;
    end else begin
      $display("Correctly detected unsatisfiable constraints");
      $display("*-* All Tests Passed *-*");
      $finish;
    end
  end
endmodule
```

## When to Use special_cases/

### Use issue_reproductions/ when:
- You have a specific bug report or GitHub issue
- The test is minimal and focused on one problem
- The issue doesn't fit a standard test category
- You want to track a regression

### Use edge_cases/ when:
- Testing boundary conditions
- Testing unusual but valid constructs
- Testing error detection/handling
- Exploring solver limits
- Testing combinations that are rare in practice

### DON'T use special_cases/ when:
- There's a better fit in the main directory structure
- Example: Basic unique constraints → use `constraint_blocks/uniqueness/`
- Example: Dynamic array randomization → use `rand_variables/arrays/dynamic/`

## Migration Notes

During the 2025-01-12 reorganization, the following were moved here:

**From `case_from_issues/`**:
- All `t_fuxian*.sv` tests → `issue_reproductions/`
- All `t_issue_*.sv` tests → `issue_reproductions/`

**From various `*_failed/` subdirectories**:
- Tests that fail due to known Verilator limitations → documented in README
- Tests that uncover new bugs → `issue_reproductions/` with issue filed

**From `constraint_blocks/`**:
- `t_constraint_unsat.sv` → `edge_cases/` (tests unsatisfiable constraints)

## Documenting Known Failures

If a test in `issue_reproductions/` is expected to fail with current Verilator:

1. Add `KNOWN_FAILURE` marker in test:
   ```systemverilog
   // KNOWN_FAILURE: Verilator master as of 2025-01-12
   // Reason: Global constraints with polymorphism not yet supported
   // Issue: https://github.com/verilator/verilator/issues/xxxx
   ```

2. Test should still be runnable and should fail in the expected way

3. Document in this README under "Known Failing Tests" section below

## Known Failing Tests

(To be updated as tests are migrated)

| Test | Status | Issue | Expected Fix |
|------|--------|-------|--------------|
| TBD  | TBD    | TBD   | TBD          |

## Related Sections

- [constraint_blocks/](../constraint_blocks/) - Standard constraint tests
- [rand_variables/](../rand_variables/) - Random variable type tests
- All other standard categories should be checked first before using special_cases/
