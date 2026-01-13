# Constraint Blocks Tests

Tests for SystemVerilog constraint blocks (IEEE 1800-2023 §18.5).

## IEEE Reference

**IEEE 1800-2023 Chapter 18.5: Constraint blocks**

Constraint blocks define the set of constraints that apply to random variables within a class. They specify legal values and relationships between random variables.

## Subdirectories

### basic/
Basic constraint block syntax and simple constraints.

**IEEE §18.5** - General constraint block syntax, operators, and basic expressions.

### external/
External constraint blocks defined outside the class.

**IEEE §18.5.1** - `constraint` keyword with `extern` modifier, allowing constraints to be defined in a different scope.

### inheritance/
Constraint inheritance and override in derived classes.

**IEEE §18.5.2** - How constraints are inherited, extended, and can be overridden in class hierarchies.

### distribution/
Distribution constraints using the `dist` operator.

**IEEE §18.5.3** - Weighted random distributions for specifying probability of values or ranges.

Example:
```systemverilog
constraint c_dist {
  x dist {0 := 10, [1:3] := 30, 4 :/ 40};
}
```

### uniqueness/
Uniqueness constraints ensuring distinct values.

**IEEE §18.5.4** - `unique` keyword for constraining arrays or sets of variables to have distinct values.

Example:
```systemverilog
constraint c_unique {
  unique {a, b, c, d};
}
```

### implication/
Implication constraints (if-then relationships).

**IEEE §18.5.5** - `->` operator for implication constraints.

Example:
```systemverilog
constraint c_impl {
  (mode == WRITE) -> (addr < 100);
}
```

### conditional/
if-else constraints for conditional randomization.

**IEEE §18.5.6** - `if-else` statements within constraint blocks.

Example:
```systemverilog
constraint c_cond {
  if (mode == READ)
    addr inside {[0:255]};
  else
    addr inside {[256:511]};
}
```

### iterative/
Iterative constraints (foreach and array reduction).

**IEEE §18.5.7** - Constraints that iterate over arrays or apply reduction operations.

#### iterative/foreach/
foreach constraints for array element constraints.

**IEEE §18.5.7.1** - `foreach` construct to constrain array elements.

Example:
```systemverilog
constraint c_foreach {
  foreach (arr[i]) arr[i] inside {[0:100]};
}
```

#### iterative/reduction/
Array reduction constraints (sum, product, etc.).

**IEEE §18.5.7.2** - Array reduction methods in constraints.

Example:
```systemverilog
constraint c_sum {
  arr.sum() == 100;
}
```

### global/
Global constraints that reference members of nested objects.

**IEEE §18.5.8** - Constraints in a class that reference members of nested class instances.

Example:
```systemverilog
class Outer;
  rand Inner inner;
  constraint c_global {
    inner.val < 100;  // Global constraint
  }
endclass
```

### ordering/
Variable ordering with solve...before.

**IEEE §18.5.9** - `solve...before` directive to control the order of variable randomization.

Example:
```systemverilog
constraint c_order {
  solve x before y;
  y == x * 2;
}
```

### static/
Static constraint blocks.

**IEEE §18.5.10** - `static` constraint blocks that are shared across all instances of a class.

### functions/
Functions used within constraints.

**IEEE §18.5.11** - Using functions (must be pure or automatic) within constraint expressions.

Example:
```systemverilog
function int check_val(int x);
  return (x > 0) && (x < 100);
endfunction

constraint c_func {
  check_val(val);
}
```

## Common Test Patterns

1. **Basic functionality** - Tests that the constraint type works as specified
2. **Edge cases** - Boundary conditions, empty arrays, extreme values
3. **Combinations** - Multiple constraint types working together
4. **Inheritance** - How constraints interact with class inheritance
5. **Error detection** - Invalid syntax or unsatisfiable constraints

## Related Sections

- [rand_variables/](../rand_variables/) - Variables that can be randomized
- [randomization_methods/](../randomization_methods/) - Methods to invoke randomization
- [constraint_control/](../constraint_control/) - Controlling constraints at runtime
