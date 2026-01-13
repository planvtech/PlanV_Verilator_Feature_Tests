# Randomization Tests Refactoring Plan

## Current Status
- **Total Tests**: 126 SystemVerilog files
- **Main Issues**:
  - Status subdirectories mixed with source (`passed/`, `failed/`, `to_test/`, etc.)
  - Unclear naming (e.g., `t_1.sv`, `t_2.sv`, `t_bad.sv`)
  - Flat structure in some areas, over-nested in others

## IEEE 1800-2023 Chapter 18 Structure

Based on IEEE 1800-2023, the randomization features are organized as follows:

```
18. Constrained random value generation
├── 18.1  General
├── 18.2  Overview
├── 18.3  Concepts and usage
├── 18.4  Random variables
│   ├── 18.4.1  Rand modifier
│   └── 18.4.2  Randc modifier
├── 18.5  Constraint blocks
│   ├── 18.5.1  External constraint blocks
│   ├── 18.5.2  Constraint inheritance
│   ├── 18.5.3  Distribution
│   ├── 18.5.4  Uniqueness constraints
│   ├── 18.5.5  Implication
│   ├── 18.5.6  if–else constraints
│   ├── 18.5.7  Iterative constraints
│   │   ├── 18.5.7.1  foreach iterative constraints
│   │   └── 18.5.7.2  Array reduction iterative constraints
│   ├── 18.5.8  Global constraints
│   ├── 18.5.9  Variable ordering
│   ├── 18.5.10 Static constraint blocks
│   └── 18.5.11 Functions in constraints
├── 18.6  Randomization methods
├── 18.7  In-line constraints—randomize() with {}
├── 18.8  Disabling random variables with rand_mode()
├── 18.9  Controlling constraints with constraint_mode()
├── 18.10 Dynamic constraint modification
├── 18.11 Inline random variable control
├── 18.12 Randomization of scope variables—std::randomize()
├── 18.13 Random number system functions and methods
├── 18.14 Random stability
├── 18.15 Manually seeding randomize
├── 18.16 Random weighted case—randcase
└── 18.17 Random sequence generation—randsequence
```

## Proposed Directory Structure

```
planv_tests/feature_tests/randomization/
├── rand_variables/                          # §18.4 Random variables
│   ├── basic_types/                         # Basic int, bit, byte, etc.
│   ├── randc/                               # §18.4.2 Randc modifier
│   ├── arrays/                              # Arrays (dynamic, assoc, queue, etc.)
│   │   ├── dynamic/
│   │   ├── associative/
│   │   ├── queue/
│   │   ├── packed/
│   │   └── unpacked/
│   ├── struct_union/                        # Struct and union types
│   └── README.md
├── constraint_blocks/                       # §18.5 Constraint blocks
│   ├── basic/                               # Basic constraint syntax
│   ├── external/                            # §18.5.1 External constraints
│   ├── inheritance/                         # §18.5.2 Constraint inheritance
│   ├── distribution/                        # §18.5.3 Distribution (dist)
│   ├── uniqueness/                          # §18.5.4 Uniqueness constraints
│   ├── implication/                         # §18.5.5 Implication
│   ├── conditional/                         # §18.5.6 if-else constraints
│   ├── iterative/                           # §18.5.7 Iterative constraints
│   │   ├── foreach/                         # §18.5.7.1 foreach
│   │   └── reduction/                       # §18.5.7.2 Array reduction
│   ├── global/                              # §18.5.8 Global constraints
│   ├── ordering/                            # §18.5.9 solve...before
│   ├── static/                              # §18.5.10 Static constraints
│   ├── functions/                           # §18.5.11 Functions in constraints
│   └── README.md
├── randomization_methods/                   # §18.6 Randomization methods
│   ├── basic/                               # Basic randomize() calls
│   ├── inline_constraints/                  # §18.7 randomize() with {}
│   └── README.md
├── constraint_control/                      # §18.8-18.11 Constraint control
│   ├── rand_mode/                           # §18.8 rand_mode()
│   ├── constraint_mode/                     # §18.9 constraint_mode()
│   ├── soft_constraints/                    # Soft constraints
│   └── README.md
├── std_randomize/                           # §18.12 std::randomize()
│   ├── basic/
│   ├── invalid_usage/                       # Error detection tests
│   └── README.md
├── random_stability/                        # §18.14 Random stability
│   └── README.md
├── randcase/                                # §18.16 randcase
│   └── README.md
├── special_cases/                           # Special scenarios
│   ├── issue_reproductions/                 # GitHub issue reproductions
│   └── edge_cases/                          # Edge cases and corner scenarios
└── README.md
```

## Enhanced Naming Convention

### Template with Optional Scope Field

```
t_<category>_<subcategory>_<feature>_<variant>.sv

<category>:     Top-level feature area (e.g., rand, constraint, std)
<subcategory>:  More specific classification (optional, e.g., array, global, dist)
<feature>:      Specific feature being tested
<variant>:      Variant/scenario (optional, e.g., basic, edge, issue1234)
```

### Examples

| Current Name | New Name | Rationale |
|--------------|----------|-----------|
| `t_1.sv` | `t_constraint_global_nested_membersel.sv` | Tests global constraints with nested member access and array selection |
| `t_2.sv` | `t_constraint_inheritance_nested_classes.sv` | Tests constraint inheritance with deeply nested classes |
| `t_bad.sv` | `t_std_randomize_invalid_args.sv` | Tests error detection for invalid std::randomize() arguments |
| `t_arr_sel.sv` | `t_constraint_global_array_selection.sv` | Tests global constraints with array element selection |
| `t_constraint_dist.sv` | ✅ Keep (already well-named) | - |
| `t_fuxian.sv` | `t_issue_fuxian_randomize_basic.sv` → move to `special_cases/issue_reproductions/` | Issue reproduction |

## File-by-File Analysis

### Files Needing Rename/Move

#### 1. Files in `to_test/` subdirectory (needs validation first)

| File | Purpose (from content) | Suggested New Name | Target Directory |
|------|----------------------|-------------------|------------------|
| `t_1.sv` | Global constraints with nested member selection and array indexing | `t_constraint_global_nested_membersel.sv` | `constraint_blocks/global/` |
| `t_2.sv` | Constraint inheritance with nested classes | `t_constraint_inheritance_nested_classes.sv` | `constraint_blocks/inheritance/` |
| `t_arr_sel.sv` | Global constraints with array element selection | `t_constraint_global_array_selection.sv` | `constraint_blocks/global/` |
| `t_poly.sv` | (Need to read) | TBD | TBD |
| `t_global_off_1.sv` | (Need to read) | TBD | TBD |
| `t_global_rand.sv` | (Duplicate?) | TBD (check if duplicate) | TBD |
| `t_global_rand_t2.sv` | (Duplicate?) | TBD (check if duplicate) | TBD |

#### 2. Files in `std_randomize/` with unclear names

| File | Purpose | Suggested New Name | Target Directory |
|------|---------|-------------------|------------------|
| `t_bad.sv` | Invalid std::randomize() args (error detection) | `t_std_randomize_invalid_args.sv` | `std_randomize/invalid_usage/` |
| `t_error.sv` | (Need to read) | TBD | TBD |
| `t_no_args.sv` | std::randomize() with no arguments | `t_std_randomize_no_args.sv` | `std_randomize/basic/` |
| `t_two_errors.sv` | (Need to read) | TBD | TBD |

#### 3. Issue reproduction files (move to `special_cases/issue_reproductions/`)

All `t_fuxian*.sv` and `t_issue_*.sv` files should be moved but keep original names:
- `t_fuxian.sv` → `special_cases/issue_reproductions/t_issue_fuxian_randomize_basic.sv`
- `t_fuxian_inherit.sv` → `special_cases/issue_reproductions/t_issue_fuxian_inherit.sv`
- `t_fuxian_pkg.sv` → `special_cases/issue_reproductions/t_issue_fuxian_pkg.sv`
- `t_fuxian_randclass.sv` → `special_cases/issue_reproductions/t_issue_fuxian_randclass.sv`
- `t_fuxian_simple.sv` → `special_cases/issue_reproductions/t_issue_fuxian_simple.sv`
- `t_fuxian_uvm_components.sv` → `special_cases/issue_reproductions/t_issue_fuxian_uvm_components.sv`
- `t_fuxian_uvm.sv` → `special_cases/issue_reproductions/t_issue_fuxian_uvm.sv`
- `t_issue_1800.sv` → `special_cases/issue_reproductions/t_issue_1800.sv` (keep as is)
- `t_issue_6740.sv` → `special_cases/issue_reproductions/t_issue_6740.sv` (keep as is)

### Status Subdirectories Analysis

#### 1. `constraint_global/` subdirectories

**Status subdirs found:**
- `9_19/9_19_verilator_passed/` (1 file)
- `9_19/9_19_verilator_failed/` (4 files)
- `master/master_verilator_passed/` (9 files)
- `master/master_verilator_failed/` (7 files)
- `passed/` (10 files)
- `modify_passed/` (4 files)
- `to_test/` (10 files)
- `vsim_falied/` (1 file, note the typo)

**Strategy:**
1. Compare files in `master_verilator_passed/` with `passed/` to detect duplicates
2. Files in `to_test/` should be validated locally:
   - If pass → rename and move to proper category
   - If fail → move to `special_cases/known_failures/` with analysis
3. Files in `*_failed/` subdirs → investigate failure reason:
   - If Verilator bug → move to `special_cases/known_failures/`
   - If test issue → archive
4. `modify_passed/` → likely older versions, compare with current tests

#### 2. `std_randomize/` subdirectories

**Status subdirs found:**
- `passed/` (3 files)
- `failed/` (2 files)
- `passed_but_need_warning/` (2 files)

**Strategy:**
1. `passed/` → compare with parent dir tests for duplicates
2. `failed/` → determine if they should fail (negative tests) or are broken
3. `passed_but_need_warning/` → special category, might need separate handling

## Well-Named Files (Keep Structure, Minor Reorganization)

### `constraint_blocks/` - Already good (27 files)
Most files are well-named. Need to:
1. Create subdirectories based on IEEE sections
2. Move files to appropriate subdirs
3. Example:
   - `t_constraint_dist.sv` → `constraint_blocks/distribution/t_constraint_dist.sv`
   - `t_constraint_unique*.sv` → `constraint_blocks/uniqueness/` (already in separate dir)
   - `t_constraint_foreach.sv` → `constraint_blocks/iterative/foreach/`
   - `t_constraint_global.sv` → `constraint_blocks/global/`
   - `t_constraint_static.sv` → `constraint_blocks/static/`

### `random_variables/` - Already good structure (33 files)
- `random_variables/Array/` → rename to `random_variables/arrays/`
- Files like `t_rand_*.sv` and `t_constraint_*.sv` → keep but organize by array type

## Migration Workflow

### Phase 1: Validate `to_test/` Files (1-2 days)

1. Run each test locally
2. Document pass/fail status
3. For passing tests: determine proper categorization
4. For failing tests: analyze why they fail

### Phase 2: Duplicate Detection (1 day)

1. Generate file content hashes
2. Compare files across `passed/`, `master_verilator_passed/`, etc.
3. Identify exact duplicates and near-duplicates
4. Create deduplication report

### Phase 3: Create New Directory Structure (0.5 day)

1. Create all target directories
2. Create README.md templates for each category
3. Create `.gitkeep` files if needed

### Phase 4: Rename and Move (2-3 days)

1. Process well-named files first (simple moves)
2. Rename unclear files based on content analysis
3. Move issue reproductions
4. Handle status subdirs

### Phase 5: Archive (0.5 day)

1. Move all status subdirs to `_archived/20250112_pre_refactor/`
2. Archive duplicates
3. Archive broken tests with notes

### Phase 6: Documentation (1 day)

1. Write README.md for each category (with IEEE references)
2. Create MIGRATION_MAP.csv
3. Update project CLAUDE.md

## Next Steps

1. **Read remaining unclear files** to understand their purpose:
   - `t_poly.sv`
   - `t_global_off_1.sv`
   - `t_error.sv`
   - `t_two_errors.sv`

2. **Generate detailed migration mapping** (CSV format)

3. **Create automation scripts**:
   - `validate_to_test.sh` - Run tests in `to_test/` subdirs
   - `detect_duplicates.sh` - Find duplicate files
   - `migrate_tests.sh` - Automated migration with safety checks

4. **User approval** before executing migration

Would you like me to:
1. Read the remaining unclear files and complete the analysis?
2. Generate the automation scripts?
3. Create the README.md templates for each category?
4. Start with duplicate detection?
