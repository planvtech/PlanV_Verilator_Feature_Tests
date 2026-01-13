# Random Variables Tests

Tests for SystemVerilog random variables (IEEE 1800-2023 §18.4).

## IEEE Reference

**IEEE 1800-2023 Chapter 18.4: Random variables**

Random variables are class properties declared with the `rand` or `randc` keyword. When `randomize()` is called, the solver assigns values to these variables while satisfying all active constraints.

## Variable Modifiers

### `rand`
Variables declared with `rand` can be assigned any legal value on each randomization, with uniform distribution by default (unless constrained).

```systemverilog
class Packet;
  rand int length;
  rand bit [7:0] data[];
endclass
```

### `randc` (Random Cyclic)
Variables declared with `randc` cycle through all possible values before repeating. See `randc/` subdirectory.

**IEEE §18.4.2**

```systemverilog
class Test;
  randc bit [2:0] value;  // Will cycle 0,1,2,3,4,5,6,7 before repeating
endclass
```

## Subdirectories

### basic_types/
Basic SystemVerilog data types as random variables.

- `int`, `bit`, `byte`, `shortint`, `longint`
- `logic` types
- Signed vs unsigned
- `real` types (limited constraint support)

Example tests:
- `t_rand_basic_types.sv` - Various basic types
- `t_constraint_basic_types.sv` - Constraints on basic types
- `t_rand_real_type.sv` - Real number randomization

### randc/
Random cyclic variables (§18.4.2).

Tests for `randc` modifier behavior:
- Cycling through all values
- Reset behavior
- randc with constraints

### arrays/
Array types as random variables.

#### arrays/dynamic/
Dynamic arrays (`int arr[]`).

Features:
- Random array size
- Constraints on size and elements
- Array method constraints (`.size()`, `.sum()`, etc.)

#### arrays/associative/
Associative arrays with various index types.

Subtests:
- String indices
- Integer indices
- 64-bit and wider indices
- User-defined type indices
- Class type indices
- Wildcard indices (`[*]`)

#### arrays/queue/
Queue types (`int q[$]`).

Features:
- Random queue size
- Element constraints
- Queue-specific constraints

#### arrays/packed/
Packed arrays (`bit [7:0][3:0] arr`).

Features:
- Multi-dimensional packed arrays
- Constraints on packed dimensions
- Bit-level access

#### arrays/unpacked/
Unpacked arrays (`int arr[10]` or `int arr[10][20]`).

Features:
- Fixed-size unpacked arrays
- Multi-dimensional arrays
- Element-wise constraints

#### arrays/mixed/
Tests combining multiple array types.

Examples:
- Dynamic array of queues
- Associative array of dynamic arrays
- Mixed packed/unpacked

### struct_union/
Struct and union types as random variables.

#### Structs
```systemverilog
typedef struct {
  rand int x;
  rand int y;
} Point;

class Test;
  rand Point p;
endclass
```

Features:
- Randomizing struct members
- Constraints on struct fields
- Nested structs
- Packed structs

#### Unions
```systemverilog
typedef union {
  int i;
  real r;
} Data;

class Test;
  rand Data d;
endclass
```

Features:
- Union randomization (random member selection)
- Constraints on active member
- Tagged unions

## Test Coverage

Each subdirectory should include:

1. **Basic tests** - Verify randomization works for the type
2. **Constraint tests** - Apply various constraints to the type
3. **Edge cases** - Empty arrays, max/min values, boundary conditions
4. **Complex scenarios** - Nested types, multiple constraints, inheritance

## Common Patterns

### No Constraints
Tests named `t_rand_*.sv` typically test randomization without constraints:
```systemverilog
class Test;
  rand int x;
endclass

// Just verify randomize() succeeds and values change
```

### With Constraints
Tests named `t_constraint_*.sv` apply constraints:
```systemverilog
class Test;
  rand int x;
  constraint c { x inside {[10:20]}; }
endclass

// Verify randomized values satisfy constraints
```

## Related Sections

- [constraint_blocks/](../constraint_blocks/) - Constraint block syntax and types
- [randomization_methods/](../randomization_methods/) - Methods to randomize variables
- [constraint_control/](../constraint_control/) - Runtime control of randomization
