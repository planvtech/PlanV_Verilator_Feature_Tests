# Randomization Feature Tests

This directory contains tests for SystemVerilog constrained random value generation features, organized according to IEEE 1800-2023 Chapter 18.

## IEEE 1800-2023 Reference

All tests in this directory correspond to **Chapter 18: Constrained random value generation** of the IEEE 1800-2023 SystemVerilog standard.

## Directory Structure

```
randomization/
├── rand_variables/              # §18.4 Random variables
│   ├── basic_types/             # Basic data types (int, bit, byte, etc.)
│   ├── randc/                   # §18.4.2 Randc (random cyclic) modifier
│   ├── arrays/                  # Array types
│   │   ├── dynamic/             # Dynamic arrays
│   │   ├── associative/         # Associative arrays
│   │   ├── queue/               # Queues
│   │   ├── packed/              # Packed arrays
│   │   ├── unpacked/            # Unpacked arrays
│   │   └── mixed/               # Mixed array type tests
│   └── struct_union/            # Struct and union types
├── constraint_blocks/           # §18.5 Constraint blocks
│   ├── basic/                   # Basic constraint syntax
│   ├── external/                # §18.5.1 External constraint blocks
│   ├── inheritance/             # §18.5.2 Constraint inheritance
│   ├── distribution/            # §18.5.3 Distribution (dist operator)
│   ├── uniqueness/              # §18.5.4 Uniqueness constraints
│   ├── implication/             # §18.5.5 Implication constraints
│   ├── conditional/             # §18.5.6 if-else constraints
│   ├── iterative/               # §18.5.7 Iterative constraints
│   │   ├── foreach/             # §18.5.7.1 foreach constraints
│   │   └── reduction/           # §18.5.7.2 Array reduction constraints
│   ├── global/                  # §18.5.8 Global constraints
│   ├── ordering/                # §18.5.9 Variable ordering (solve...before)
│   ├── static/                  # §18.5.10 Static constraint blocks
│   └── functions/               # §18.5.11 Functions in constraints
├── randomization_methods/       # §18.6-18.7 Randomization methods
│   ├── basic/                   # Basic randomize() method calls
│   └── inline_constraints/      # §18.7 randomize() with {} syntax
├── constraint_control/          # §18.8-18.11 Constraint control
│   ├── rand_mode/               # §18.8 rand_mode() method
│   ├── constraint_mode/         # §18.9 constraint_mode() method
│   └── soft_constraints/        # Soft constraints
├── std_randomize/               # §18.12 std::randomize()
│   ├── basic/                   # Basic scope variable randomization
│   └── invalid_usage/           # Error detection and invalid usage tests
├── random_stability/            # §18.14 Random stability
├── randcase/                    # §18.16 randcase statement
└── special_cases/               # Special scenarios
    ├── issue_reproductions/     # GitHub issue reproductions
    └── edge_cases/              # Edge cases and corner scenarios
```

## Test Naming Convention

All test files follow the naming pattern:

```
t_<category>_<subcategory>_<feature>_<variant>.sv
```

Where:
- **category**: Top-level feature (e.g., `rand`, `constraint`, `std`)
- **subcategory**: More specific classification (e.g., `array`, `global`, `dist`)
- **feature**: Specific feature being tested
- **variant**: Optional variant/scenario (e.g., `basic`, `v1`, `edge`)

### Examples

- `t_rand_basic_types.sv` - Random variables with basic data types
- `t_constraint_dist.sv` - Distribution constraints
- `t_constraint_global_nested_membersel.sv` - Global constraints with nested member selection
- `t_std_randomize_scope_vars.sv` - std::randomize() with scope variables
- `t_issue_fuxian_randomize_basic.sv` - Issue reproduction test

## Test File Requirements

All test files must follow the PlanV Feature Tests format:

1. **File and module names must match**:
   ```systemverilog
   // File: t_constraint_dist.sv
   module t_constraint_dist;
   ```

2. **File header**:
   ```systemverilog
   // DESCRIPTION: PlanV Verilator Feature Tests
   //
   // Property of PlanV GmbH, 2025. All rights reserved.
   // Contact: yilou.wang@planv.tech
   ```

3. **Success indication**:
   ```systemverilog
   $display("*-* All Tests Passed *-*");
   $finish;
   ```

## Running Tests

Use the PlanV test framework:

```bash
cd /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests
./scripts/run -b master -t planv_tests/feature_tests/randomization
```

To run a specific subcategory:

```bash
./scripts/run -b master -t planv_tests/feature_tests/randomization/constraint_blocks/global
```

## Contributing

When adding new tests:

1. Determine the correct subcategory based on IEEE 1800-2023 chapter structure
2. Follow the naming convention
3. Include proper file header
4. Add test description in comments
5. Ensure test passes with current Verilator master branch

## Migration History

This directory structure was created on 2025-01-12 during the randomization tests reorganization project. See `MIGRATION_MAP.csv` for the complete mapping from old to new file locations.

Previous structure (archived at `_archived/20250112_pre_refactor/`):
- `constrained_random/constraint_blocks/`
- `constrained_random/constraint_global/`
- `constrained_random/constraint_unique/`
- `constrained_random/random_variables/`
- `constrained_random/std_randomize/`
- `constrained_random/case_from_issues/`

## Related Documentation

- IEEE 1800-2023 Standard (Chapter 18)
- [Verilator Manual - Randomization](https://verilator.org/guide/latest/exe_verilator.html#randomization)
- PlanV Verilator Feature Tests README
