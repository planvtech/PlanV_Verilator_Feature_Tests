# PlanV Verilator Feature Tests

SystemVerilog feature validation tests for PlanV's Verilator enhancements.

## Directory Structure

Tests are organized by IEEE 1800-2023 chapter numbers:

```
├── 00_issue_reproductions/    # Real-world bug reproductions
│   ├── interfaces/
│   ├── randomization/
│   ├── simulation/
│   └── timing/
│
├── 10_assignment_statements/  # Chapter 10: Assignment patterns
├── 12_control_flow/           # Chapter 12: Loops and control flow
│   └── loops/
│
├── 16_assertions/             # Chapter 16: Assertions
│   ├── concurrent/
│   ├── coverage/
│   └── immediate/
│
├── 18_randomization/          # Chapter 18: Constrained random
│   ├── constraint_blocks/     # Constraint syntax
│   ├── constraint_control/    # rand_mode, constraint_mode
│   ├── global_constraints/    # Constraints on nested members
│   ├── randcase/              # randcase statements
│   ├── randomization_methods/ # randomize() with inline constraints
│   ├── random_stability/      # Deterministic randomization
│   ├── rand_variables/        # rand/randc variable types
│   └── std_randomize/         # std::randomize() function
│
├── 19_functional_coverage/    # Chapter 19: Coverage
│   ├── bins/                  # Bin types (basic, illegal, transition)
│   ├── conditional/           # iff conditions
│   ├── covergroup/            # Covergroup/coverpoint basics
│   └── cross/                 # Cross coverage
│
├── 25_interfaces/             # Chapter 25: Interfaces
│   ├── virtual_interface/     # Virtual interface usage
│   │   ├── basic/
│   │   ├── class/
│   │   ├── scheduler/
│   │   ├── timing/
│   │   └── values/
│   └── error_cases/
│
├── 26_timing/                 # Chapter 26: Timing controls
│   ├── basic/
│   └── race_conditions/
│
└── 27_simulation/             # Chapter 27: Simulation semantics
```

## File Naming Convention

All test files follow the pattern: `t_<category>_<specific>.sv`

**Examples:**
- `t_rand_array_assoc_basic.sv` - Randomization test for associative arrays
- `t_cov_bins_illegal.sv` - Coverage test for illegal bins
- `t_vif_class_callback.sv` - Virtual interface with class callbacks

## Test File Format

Each test file is standalone:
- **Header**: PlanV copyright, description
- **Success marker**: `$write("*-* All Finished *-*\n");`
- **Failure**: `$stop;`
- **Module name**: Matches filename (e.g., `t_foo.sv` → `module t_foo;`)

## Archived Tests

The `_archived/` directory contains old test versions preserved for reference only.
