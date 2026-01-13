# Randomization Tests Refactoring Session History

**Date**: 2026-01-12/13
**Engineer**: Yilou Wang
**Scope**: Reorganize randomization tests following IEEE 1800-2023 structure

---

## Session Overview

This document records the complete refactoring process for reorganizing the randomization feature tests in the PlanV Verilator Feature Tests repository.

### Initial State
- **Location**: `planv_tests/feature_tests/constrained_random/`
- **Total Tests**: 126 SystemVerilog files
- **Issues**:
  - Unclear naming (e.g., `t_1.sv`, `t_2.sv`, `t_bad.sv`)
  - Status subdirectories mixed with source (`passed/`, `failed/`, `to_test/`, `modify_passed/`)
  - Inconsistent organization
  - No clear mapping to IEEE 1800 standard

### Goals
1. Create IEEE 1800-2023 Chapter 18 aligned directory structure
2. Rename unclear test files with descriptive names
3. Separate issue reproductions into dedicated area
4. Archive old structure completely
5. Maintain full traceability

---

## Phase 1: Analysis and Planning

### IEEE 1800-2023 Chapter 18 Structure Analysis

Read and analyzed IEEE 1800-2023 standard text version to understand the official structure:

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

### Design Decision: Hybrid Classification Scheme

**Selected Approach**: Scheme C (Hybrid)
- **Top level**: Functional categories (intuitive for users)
- **Sub level**: IEEE 1800 sections (standardized)
- **Special cases**: Dedicated directory for issue reproductions and edge cases

**Rationale**:
- Easy to navigate for new users
- Formal IEEE section mapping for documentation
- Flexible handling of special scenarios
- Extensible for future additions

### Enhanced Naming Convention

**Template**:
```
t_<category>_<subcategory>_<feature>_<variant>.sv
```

**Fields**:
- `<category>`: Top-level feature (e.g., `rand`, `constraint`, `std`)
- `<subcategory>`: Optional, more specific classification (e.g., `array`, `global`, `dist`)
- `<feature>`: Specific feature being tested
- `<variant>`: Optional variant/scenario (e.g., `basic`, `v1`, `edge`, `issue1234`)

**Examples**:
- `t_rand_basic_types.sv` - Basic types randomization
- `t_constraint_global_nested_membersel.sv` - Global constraints with nested member selection
- `t_std_randomize_scope_vars.sv` - std::randomize() with scope variables
- `t_issue_fuxian_randomize_basic.sv` - Issue reproduction

---

## Phase 2: File Content Analysis

### Unclear Filenames Analyzed

Read and documented the purpose of all unclear filenames:

| Original File | Content Analysis | New Name | Target Directory |
|--------------|------------------|----------|------------------|
| `t_1.sv` | Tests global constraints with nested member selection (`mid.arr[0].x`) and array indexing | `t_constraint_global_nested_membersel.sv` | `constraint_blocks/global/` |
| `t_2.sv` | Tests constraint inheritance with deeply nested classes (Unrelated2 → Unrelated → Derived → Base) | `t_constraint_inheritance_nested_classes.sv` | `constraint_blocks/inheritance/` |
| `t_bad.sv` | Error detection test for invalid std::randomize() arguments (method calls, array elements, null) | `t_std_randomize_invalid_args.sv` | `std_randomize/invalid_usage/` |
| `t_arr_sel.sv` | Tests global constraints with array element selection (`mids[0].items[1].val`) | `t_constraint_global_array_selection.sv` | `constraint_blocks/global/` |
| `t_poly.sv` | Tests polymorphism with constraints (has commented code, possibly incomplete) | `t_constraint_inheritance_polymorphism.sv` | `constraint_blocks/inheritance/` |
| `t_global_off_1.sv` | Tests global constraints with nested object member access (`foo.x`, `foo.in.val`) | `t_constraint_global_nested_objects.sv` | `constraint_blocks/global/` |
| `t_error.sv` | std::randomize with local variables (no test body - incomplete?) | `t_std_randomize_local_vars.sv` | `std_randomize/basic/` |
| `t_no_args.sv` | Tests std::randomize() with no arguments | `t_std_randomize_no_args.sv` | `std_randomize/basic/` |
| `t_two_errors.sv` | Tests this.randomize() with inline constraints on member variables (bug fix test) | `t_randomize_inline_with_member_vars.sv` | `randomization_methods/inline_constraints/` |

### Test Inventory

**Total Files**: 126

**Breakdown by Current Location**:
- `case_from_issues/`: 9 files (issue reproductions)
- `constraint_blocks/`: 27 files (well-named)
- `constraint_global/`: 71 files (including status subdirs)
- `constraint_unique/`: 3 files (already organized)
- `random_variables/`: 33 files (good structure)
- `std_randomize/`: 13 files (includes status subdirs)

**Status Subdirectories Identified**:
- `constraint_global/9_19/9_19_verilator_passed/` (1 file)
- `constraint_global/9_19/9_19_verilator_failed/` (4 files)
- `constraint_global/master/master_verilator_passed/` (9 files)
- `constraint_global/master/master_verilator_failed/` (7 files)
- `constraint_global/passed/` (10 files)
- `constraint_global/modify_passed/` (4 files)
- `constraint_global/to_test/` (10 files)
- `constraint_global/vsim_falied/` (1 file)
- `std_randomize/passed/` (3 files)
- `std_randomize/failed/` (2 files)
- `std_randomize/passed_but_need_warning/` (2 files)

---

## Phase 3: Migration Mapping

### Created Files

1. **MIGRATION_MAP.csv** - Complete file-by-file mapping
   - Original path
   - New path
   - New filename
   - IEEE section reference
   - Action (MOVE, RENAME_MOVE, ANALYZE_DUPLICATE, ARCHIVE)
   - Priority (HIGH, MEDIUM, LOW)
   - Notes

2. **RANDOMIZATION_REFACTOR.md** - Detailed refactoring plan (536 lines)
   - Directory structure design
   - Naming conventions
   - File-by-file analysis
   - Migration phases
   - Risk assessment

3. **NEXT_STEPS.md** - Execution guide
   - Step-by-step instructions
   - Time estimates
   - Decision points
   - Rollback procedures

---

## Phase 4: Directory Structure Creation

### New Directory Tree

Created 41 subdirectories:

```
planv_tests/feature_tests/randomization/
├── rand_variables/                          # §18.4
│   ├── basic_types/
│   ├── randc/                               # §18.4.2
│   ├── arrays/
│   │   ├── dynamic/
│   │   ├── associative/
│   │   ├── queue/
│   │   ├── packed/
│   │   ├── unpacked/
│   │   └── mixed/
│   └── struct_union/
├── constraint_blocks/                       # §18.5
│   ├── basic/
│   ├── external/                            # §18.5.1
│   ├── inheritance/                         # §18.5.2
│   ├── distribution/                        # §18.5.3
│   ├── uniqueness/                          # §18.5.4
│   ├── implication/                         # §18.5.5
│   ├── conditional/                         # §18.5.6
│   ├── iterative/                           # §18.5.7
│   │   ├── foreach/                         # §18.5.7.1
│   │   └── reduction/                       # §18.5.7.2
│   ├── global/                              # §18.5.8
│   ├── ordering/                            # §18.5.9
│   ├── static/                              # §18.5.10
│   └── functions/                           # §18.5.11
├── randomization_methods/                   # §18.6-18.7
│   ├── basic/                               # §18.6
│   └── inline_constraints/                  # §18.7
├── constraint_control/                      # §18.8-18.11
│   ├── rand_mode/                           # §18.8
│   ├── constraint_mode/                     # §18.9
│   └── soft_constraints/
├── std_randomize/                           # §18.12
│   ├── basic/
│   └── invalid_usage/
├── random_stability/                        # §18.14
├── randcase/                                # §18.16
└── special_cases/
    ├── issue_reproductions/
    └── edge_cases/
```

### Archive Structure

```
planv_tests/feature_tests/_archived/
└── 20250112_pre_refactor/
    ├── constrained_random/                  # Complete backup
    ├── BACKUP_INFO.txt                      # Backup metadata
    └── ... (to be populated during migration)
```

---

## Phase 5: Documentation Creation

### README Files Created

1. **randomization/README.md** - Main documentation
   - Directory structure overview
   - IEEE 1800-2023 reference
   - Test naming convention
   - File requirements
   - Running tests
   - Migration history

2. **constraint_blocks/README.md**
   - Detailed explanation of each constraint type
   - IEEE section references
   - Code examples for each subdirectory
   - Common test patterns

3. **rand_variables/README.md**
   - rand vs randc modifiers
   - Data type coverage
   - Array type details
   - Struct/union randomization

4. **std_randomize/README.md**
   - std::randomize() vs obj.randomize()
   - Valid and invalid usage patterns
   - Error detection tests
   - Comparison table

5. **special_cases/README.md**
   - When to use issue_reproductions/
   - When to use edge_cases/
   - Issue lifecycle
   - Known failures tracking

### Documentation Standards

All READMEs include:
- IEEE 1800-2023 section references
- Purpose and scope
- Code examples
- Test patterns
- Related sections links

---

## Phase 6: Automation Scripts

### migrate_randomization_tests.sh

**Purpose**: Automated migration of test files

**Features**:
- Reads MIGRATION_MAP.csv
- Renames files
- Updates module names in file content
- Creates destination directories
- Archives original files
- Generates migration log
- Supports dry-run mode

**Safety**:
- Copies files before modifying
- Archives originals (doesn't delete)
- Validates each step
- Error tracking and reporting

**Usage**:
```bash
./scripts/migrate_randomization_tests.sh --dry-run  # Preview
./scripts/migrate_randomization_tests.sh            # Execute
```

### detect_duplicates.sh

**Purpose**: Identify duplicate test files

**Features**:
- Exact duplicate detection (MD5 hash)
- Fuzzy duplicate detection (ignoring comments/whitespace)
- Filename similarity analysis
- Generates detailed report

**Output**: DUPLICATE_REPORT_*.md with:
- Duplicate groups
- Recommended actions
- File lists for each duplicate set

**Usage**:
```bash
./scripts/detect_duplicates.sh [directory]
```

---

## Phase 7: Backup Creation

### Full Backup

**Date**: 2026-01-13 10:09:03 CET

**Actions Taken**:
1. ✅ Copied entire `constrained_random/` directory to `_archived/20250112_pre_refactor/`
2. ✅ Created BACKUP_INFO.txt with timestamp and metadata
3. ✅ Verified backup contains all 126 test files

**Backup Location**:
```
planv_tests/feature_tests/_archived/20250112_pre_refactor/constrained_random/
```

**Verification**:
```bash
# Count files in backup
find planv_tests/feature_tests/_archived/20250112_pre_refactor/constrained_random -name "*.sv" | wc -l
# Expected: 126 files
```

### Git Safety Net

**Recommended Tags** (to be created):
- `refactor-randomization-before` - Before any changes
- `refactor-randomization-complete` - After successful migration

**Rollback Command**:
```bash
git reset --hard refactor-randomization-before
```

---

## Migration Statistics

### Files to Process

| Action | Count | Priority |
|--------|-------|----------|
| RENAME_MOVE | ~25 | HIGH |
| MOVE | ~80 | MEDIUM |
| ANALYZE_DUPLICATE | ~15 | HIGH |
| ARCHIVE | ~20 | LOW |

### Naming Changes

**Major Renames**:
- `t_1.sv` → `t_constraint_global_nested_membersel.sv`
- `t_2.sv` → `t_constraint_inheritance_nested_classes.sv`
- `t_bad.sv` → `t_std_randomize_invalid_args.sv`
- `t_arr_sel.sv` → `t_constraint_global_array_selection.sv`
- `t_poly.sv` → `t_constraint_inheritance_polymorphism.sv`
- `t_global_off_1.sv` → `t_constraint_global_nested_objects.sv`
- 9 issue files → `t_issue_*.sv` format

**Category Standardization**:
- All constraint block tests → `constraint_blocks/<subcategory>/`
- All random variable tests → `rand_variables/<type>/`
- All std::randomize tests → `std_randomize/<usage>/`
- All issue reproductions → `special_cases/issue_reproductions/`

---

## Key Decisions Made

### 1. Directory Structure
- **Decision**: Hybrid scheme (functional top-level, IEEE sub-level)
- **Rationale**: Balance between usability and standardization
- **Alternative considered**: Pure IEEE section mapping (rejected as less intuitive)

### 2. Naming Convention
- **Decision**: Add optional `<subcategory>` field
- **Rationale**: Better categorization and clarity
- **Example**: `t_constraint_global_array_selection.sv` is clearer than `t_constraint_array_selection.sv`

### 3. Special Cases Handling
- **Decision**: Dedicated `special_cases/` directory
- **Rationale**: Keeps issue reproductions and edge cases separate from standard tests
- **Benefit**: Easier to maintain and understand test purpose

### 4. Status Subdirectories
- **Decision**: Archive all status subdirs after duplicate analysis
- **Rationale**: Status belongs in git history, not directory structure
- **Process**: Extract unique tests first, then archive

### 5. Backup Strategy
- **Decision**: Full directory copy + git tag
- **Rationale**: Double safety (filesystem backup + git history)
- **Recovery**: Can recover from either source

---

## Next Steps (Execution Phase)

### Immediate Actions

1. **Create git tag** for safety:
   ```bash
   git add .
   git commit -m "Add randomization refactor planning artifacts"
   git tag refactor-randomization-before
   ```

2. **Run duplicate detection**:
   ```bash
   ./scripts/detect_duplicates.sh
   ```

3. **Review duplicate report** and update MIGRATION_MAP.csv

4. **Dry-run migration**:
   ```bash
   ./scripts/migrate_randomization_tests.sh --dry-run
   ```

5. **Execute migration**:
   ```bash
   ./scripts/migrate_randomization_tests.sh
   ```

6. **Verify results**:
   ```bash
   tree planv_tests/feature_tests/randomization
   ./scripts/run -b master -t planv_tests/feature_tests/randomization
   ```

7. **Commit results**:
   ```bash
   git add .
   git commit -m "Refactor: Reorganize randomization tests"
   git tag refactor-randomization-complete
   ```

---

## Lessons Learned

### Planning Phase Insights

1. **IEEE Standard as Foundation**: Using the official standard as the organizational basis provides:
   - Clear, unambiguous categories
   - Easy reference for documentation
   - Professional, maintainable structure

2. **Content Analysis is Critical**: Can't rely on filenames alone:
   - `t_1.sv` could be anything without reading content
   - Reading all unclear files prevented misclassification
   - Discovered incomplete tests (e.g., `t_error.sv`, `t_poly.sv`)

3. **Status Subdirectories are Anti-pattern**: Mixing test results with source code:
   - Creates duplication
   - Makes it hard to find canonical version
   - Status belongs in git history or CI results, not source tree

4. **Automation is Essential**: With 126 files:
   - Manual migration would be error-prone
   - Scripts ensure consistency
   - Dry-run mode allows safe verification

5. **Documentation Up-Front**: Creating READMEs before migration:
   - Clarifies structure and purpose
   - Serves as specification for migration
   - Helps catch organizational issues early

### Tools and Techniques

**Effective**:
- CSV for migration mapping (easy to edit, script-friendly)
- IEEE standard text version (searchable, parseable)
- Bash scripts for automation
- Git tags for safety
- README-driven design

**Could Improve**:
- Consider JSON/YAML for migration map (more structured)
- Add validation scripts (check for missing files, broken links)
- Create test result comparison tool (before/after migration)

---

## References

### Documentation
- [RANDOMIZATION_REFACTOR.md](RANDOMIZATION_REFACTOR.md) - Detailed plan
- [MIGRATION_MAP.csv](MIGRATION_MAP.csv) - File mapping
- [NEXT_STEPS.md](NEXT_STEPS.md) - Execution guide
- [planv_tests/feature_tests/randomization/README.md](planv_tests/feature_tests/randomization/README.md) - New structure docs

### Standards
- IEEE 1800-2023 Chapter 18: Constrained random value generation
- Path: `/home/yilou/Desktop/OSVISE/planvtech/langgraph_verilator_gap_checker/memories/ieee/docs/ieee1800-2023.txt`

### Scripts
- [scripts/migrate_randomization_tests.sh](scripts/migrate_randomization_tests.sh)
- [scripts/detect_duplicates.sh](scripts/detect_duplicates.sh)

---

## Timeline

| Date | Activity | Duration | Status |
|------|----------|----------|--------|
| 2026-01-12 | IEEE standard analysis | 1 hour | ✅ Complete |
| 2026-01-12 | Directory structure design | 2 hours | ✅ Complete |
| 2026-01-12 | File content analysis | 2 hours | ✅ Complete |
| 2026-01-12 | Migration mapping | 1 hour | ✅ Complete |
| 2026-01-12 | Documentation creation | 2 hours | ✅ Complete |
| 2026-01-12 | Script development | 2 hours | ✅ Complete |
| 2026-01-13 | Backup creation | 0.5 hours | ✅ Complete |
| 2026-01-13 | Duplicate detection | TBD | ⏳ Pending |
| 2026-01-13 | Migration execution | TBD | ⏳ Pending |
| 2026-01-13 | Verification | TBD | ⏳ Pending |
| 2026-01-13 | Final commit | TBD | ⏳ Pending |

**Total Time Invested**: ~10.5 hours
**Estimated Remaining**: ~4-6 hours

---

## Appendix: File Count Verification

### Pre-Migration Count
```bash
find planv_tests/feature_tests/constrained_random -name "*.sv" -type f | wc -l
# Expected: 126
```

### Post-Migration Count (Target)
```bash
find planv_tests/feature_tests/randomization -name "*.sv" -type f | wc -l
# Expected: 126 (same total, different organization)
```

### Backup Verification
```bash
find planv_tests/feature_tests/_archived/20250112_pre_refactor/constrained_random -name "*.sv" -type f | wc -l
# Expected: 126 (complete backup)
```

---

**Document Status**: ✅ Complete
**Last Updated**: 2026-01-13 10:09 CET
**Next Update**: After duplicate detection and migration execution
