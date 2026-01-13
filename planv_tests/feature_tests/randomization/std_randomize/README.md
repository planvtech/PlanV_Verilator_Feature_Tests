# std::randomize() Tests

Tests for scope variable randomization using `std::randomize()` (IEEE 1800-2023 §18.12).

## IEEE Reference

**IEEE 1800-2023 Chapter 18.12: Randomization of scope variables—std::randomize()**

The `std::randomize()` function allows randomization of variables in the current scope (local variables, module variables, etc.) without requiring a class instance.

## Basic Syntax

```systemverilog
initial begin
  int x, y;

  // Randomize scope variables
  if (std::randomize(x, y) with {
    x inside {[0:100]};
    y > x;
  }) begin
    $display("x=%0d, y=%0d", x, y);
  end
end
```

## Subdirectories

### basic/
Basic `std::randomize()` usage with scope variables.

Features tested:
- Single variable randomization
- Multiple variable randomization
- With and without inline constraints
- Return value checking (success/failure)
- Scope variable types (int, bit, arrays, etc.)

Example tests:
- `t_std_randomize_scope_vars.sv` - Basic scope variable randomization
- `t_std_randomize_no_args.sv` - std::randomize() with no arguments (should fail)
- `t_std_randomize_with_constraints.sv` - Inline constraints with std::randomize()
- `t_std_randomize_local_vars.sv` - Local variables in functions/tasks

### invalid_usage/
Error detection tests for invalid `std::randomize()` usage.

Invalid cases:
1. **Class member variables** - Cannot randomize class members with std::randomize():
   ```systemverilog
   class Foo;
     int x;
     function void test();
       std::randomize(x);  // INVALID - should use this.randomize()
     endfunction
   endclass
   ```

2. **Method calls as arguments**:
   ```systemverilog
   std::randomize(obj.get().x);  // INVALID
   ```

3. **Array element references**:
   ```systemverilog
   std::randomize(arr[i].member);  // May be invalid depending on context
   ```

4. **Undefined variables**:
   ```systemverilog
   std::randomize(undefined_var);  // INVALID - compile error
   ```

5. **Null references**:
   ```systemverilog
   std::randomize(null);  // INVALID
   ```

Example tests:
- `t_std_randomize_invalid_args.sv` - Various invalid argument types
- `t_std_randomize_class_member_bad_v1.sv` - Class member usage (should warn)
- `t_std_randomize_class_member_bad_v2.sv` - Another class member scenario
- `t_std_randomize_undefined_var.sv` - Undefined variable error

## Key Differences from Class Randomization

| Feature | `std::randomize()` | `obj.randomize()` |
|---------|-------------------|-------------------|
| Target | Scope variables | Class members (rand variables) |
| Context | Any scope (initial, function, task) | Class method or external call |
| Constraints | Inline only (with {}) | Class constraints + inline |
| Variable declaration | No `rand` keyword | Requires `rand` keyword |

## Common Test Patterns

### Positive Tests (basic/)
Verify that valid usage works correctly:
```systemverilog
initial begin
  int x;
  assert(std::randomize(x) with { x inside {[1:10]}; });
  assert(x >= 1 && x <= 10);
  $display("*-* All Tests Passed *-*");
  $finish;
end
```

### Negative Tests (invalid_usage/)
Verify that invalid usage is detected:
```systemverilog
class Test;
  int x;
  function void bad_usage();
    // This should generate warning/error
    void'(std::randomize(x));
  endfunction
endclass
```

Expected behavior:
- Compile-time error for clearly invalid cases
- Runtime failure (return 0) for unsatisfiable constraints
- Warning for questionable usage (e.g., class members)

## Special Cases

### passed_but_need_warning/
Some tests pass functionally but should generate warnings because they use patterns that are technically allowed but not recommended or are edge cases in the specification.

Example:
- Using std::randomize() on class members instead of obj.randomize()
- Ambiguous variable scope resolution

## Test Checklist

When adding new std::randomize() tests:

- [ ] Test with single variable
- [ ] Test with multiple variables
- [ ] Test with inline constraints (`with {}`)
- [ ] Test without constraints
- [ ] Test with unsatisfiable constraints (should return 0)
- [ ] Test with different data types
- [ ] Test return value checking
- [ ] Test invalid usage (compile errors)

## Related Sections

- [randomization_methods/](../randomization_methods/) - Class-based randomize() methods
- [constraint_blocks/](../constraint_blocks/) - Constraint syntax (also applies to inline constraints)
- [rand_variables/](../rand_variables/) - Random variable types
