# PlanV Verilator Feature Tests Project

## Project Overview
- **Project Path**: `/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests`
- **Main Branch**: `main`
- **Purpose**: Feature validation tests for PlanV-specific Verilator enhancements
- **Primary Focus**: SystemVerilog feature testing (constraints, UVM, timing, assertions, etc.)

## Project Structure

### Core Directories

```
PlanV_Verilator_Feature_Tests/
├── planv_tests/              # Test source files
│   ├── feature_tests/        # Feature validation tests (165 .sv files)
│   └── uvm_tests/            # UVM testbenches
├── sim/                      # Generated simulation artifacts (auto-created)
├── logs/                     # Test execution logs & HTML reports (auto-created)
├── scripts/                  # Build & test automation scripts
├── verilator/                # Multiple Verilator versions (submodules)
│   ├── master/               # Latest development version
│   ├── version-5.040/
│   ├── version-5.042/
│   └── version-5.044/
├── uvm_lib/                  # UVM library variants (submodules)
│   ├── uvm-2017/
│   └── uvm-antmicro-deprecatedApi/
└── .github/workflows/        # CI/CD configuration
```

### Feature Tests Categories

Located in `planv_tests/feature_tests/`:

1. **assertions** - Immediate/concurrent assertion tests (5 tests)
2. **assignment_statements** - Assignment pattern tests
3. **constrained_random** - Constraint randomization tests (largest category)
   - `case_from_issues/` - Bug reproduction cases
   - `constraint_blocks/` - Constraint block syntax tests
   - `constraint_global/` - Global constraint tests
   - `constraint_unique/` - Unique constraint tests
   - `random_variables/` - Random variable tests
   - `std_randomize/` - std::randomize tests
4. **foreach** - Foreach loop tests
5. **functional_coverage** - Coverage feature tests
6. **t_racing** - Race condition tests (4 tests)
7. **t_recursive** - Recursive module instantiation tests
8. **t_timing_debug** - Timing/delay tests
9. **t_virtual_interface** - Virtual interface tests

### UVM Tests Categories

Located in `planv_tests/uvm_tests/`:

1. **DUT** - Simple C++ testbench with Verilator
2. **GettingVerilatorStartedWithUVM** - UVM introduction examples
3. **pyuvm_test** - Python-based UVM tests (using cocotb/pyuvm)
4. **uvm_test_1** - FIFO verification testbench
5. **uvm_test_2** - Advanced UVM testbench
6. **uvm_test_cvv** - Core-V-Verif framework style testbench

## Test File Organization Patterns

### Test Status Subdirectories

Many test categories contain subdirectories indicating test status:

- **`passed/`** - Tests that pass on baseline Verilator
- **`failed/` or `*_failed/`** - Tests that currently fail
- **`error/`** - Tests that intentionally trigger errors
- **`modify_pass/`** - Tests that pass after modifications
- **`original_pass/`** - Original passing tests
- **`bug_find/`** - Bug discovery/debugging tests
- **`to_test/`** - Tests pending validation

Example structure in `constrained_random/constraint_global/`:
```
constraint_global/
├── 9_19/                     # Branch-specific test results
│   ├── 9_19_verilator_failed/
│   └── 9_19_verilator_passed/
├── master/                   # Master branch test results
│   ├── master_verilator_failed/
│   └── master_verilator_passed/
├── passed/                   # Tests passing on baseline
├── modify_passed/            # Tests passing after fixes
├── to_test/                  # Pending validation
├── vsim_failed/              # Failed on ModelSim/QuestaSim
└── *.sv                      # Active test files
```

**Issues with Current Organization:**
- Mixed status subdirectories with active test files causes confusion
- Branch-specific subdirectories (`9_19/`, `master/`) mix test results with source
- Unclear which `.sv` files are actively tested vs archived
- Difficult to identify canonical test set for CI/CD

## Test File Format

### File Naming Convention
- Single `.sv` file per test (NOT `.v` + `.sv` + `.py` like verilator/test_regress)
- File name and module name **MUST** match
- Example: `t_assertion_immediate.sv` → `module t_assertion_immediate;`

### File Header Template
```systemverilog
// DESCRIPTION: PlanV Verilator <Feature Name> Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0.
// Contact: yilou.wang@planv.tech
```

### Test Success Indicators
```systemverilog
// Success message
$display("*-* All Tests Passed *-*");

// Required termination
$finish;
```

### Key Differences from verilator/test_regress

| Aspect | verilator/test_regress | PlanV Feature Tests |
|--------|------------------------|---------------------|
| Files per test | `.v`, `.sv`, `.py` | `.sv` only |
| Success message | `$write("*-* All Finished *-*\n");` | `$display("*-* All Tests Passed *-*");` |
| Purpose | Official Verilator regression | PlanV feature validation |
| Organization | Flat directory with driver scripts | Categorized with subdirectories |
| CI Integration | Part of Verilator repo | Separate GitHub Actions workflow |

## Build & Test Workflow

### Local Testing

**Command Format:**
```bash
./scripts/run -b <branch_name> -t <test_dir/test_file>
```

**Examples:**
```bash
# Test all assertions
./scripts/run -b master -t planv_tests/feature_tests/assertions

# Test single file
./scripts/run -b master -t planv_tests/feature_tests/assertions/t_assertion_immediate.sv
```

**Process Flow:**
1. **Setup** (`scripts/setup_framework`):
   - Updates git submodules (Verilator versions, UVM libs)
   - Scans specified test directory for `.sv` files
   - Generates Makefile for each test in `sim/` directory
   - Creates directory structure mirroring `planv_tests/`

2. **Build** (`scripts/set_build_run_functions::build`):
   - Compiles specified Verilator branch in `verilator/<branch>/`
   - Uses autoconf + make
   - Logs to `logs/run.log`

3. **Run Tests** (`scripts/set_build_run_functions::run_tests`):
   - Executes each Makefile in `sim/` directory
   - Verilates `.sv` → C++ → compiles → runs simulation
   - Logs individual test output to `logs/feature_tests/<category>/<test>.log`
   - Checks for "*-* All Finished *-*" in logs for pass/fail
   - Generates summary in `logs/feature_tests/tests_report.log`
   - Creates HTML report: `logs/feature_tests/fancy_test_report_<branch>.html`

**Generated Artifacts:**
```
logs/
├── run.log                   # Setup & build logs
├── feature_tests/
│   ├── <category>/
│   │   └── <test>.log        # Individual test logs
│   ├── tests_report.log      # Summary report
│   └── fancy_test_report_<branch>.html
└── uvm_tests/
    └── <test>.log

sim/
└── feature_tests/
    └── <category>/
        └── <test>/
            └── Makefile      # Auto-generated per test
```

### CI/CD (GitHub Actions)

**Workflow:** `.github/workflows/PlanV_verilator_feature_tests.yml`

**Trigger:**
- Manual dispatch
- Push to `main` branch
- Pull requests
- Scheduled: Every Monday at 07:00 (cron: "0 7 * * 1")

**Matrix Strategy:**
- Dynamically discovers Verilator branches in `verilator/` directory
- Runs full test suite for each branch in parallel

**Steps:**
1. Checkout repo with submodules
2. Install dependencies (gcc-12, Python, z3-solver, etc.)
3. Setup: `scripts/ciSystemRunner --setup`
4. Build: `scripts/ciSystemRunner --build <branch>`
5. Run: `scripts/ciSystemRunner --run_tests <branch>`
6. Upload logs as artifacts

## Code Standards & Style

### Language Requirements
- **All code, comments, variable names**: English only
- **All communication with user**: Chinese
- **File headers**: English (template above)

### SystemVerilog Coding Conventions
- Follow IEEE 1800 SystemVerilog standard
- Module name must match filename
- Use meaningful test names (e.g., `t_constraint_unique_edge_cases`)
- Include success message and `$finish` in all tests

### Test Naming Conventions
- Prefix: `t_` for standalone tests
- Descriptive middle: feature or scenario (e.g., `constraint_unique`, `assertion_immediate`)
- Avoid cryptic abbreviations
- Examples:
  - `t_assertion_concurrent.sv`
  - `t_constraint_array_sum.sv`
  - `t_virtual_interface_member_trigger.sv`

## Development Guidelines

### Adding New Tests

**For Feature Tests:**

1. **Choose appropriate category** in `planv_tests/feature_tests/`
   - If no suitable category exists, create new directory with clear name
   - Avoid creating status subdirectories (`passed/`, `failed/`, etc.)

2. **Create single `.sv` file** with proper header and naming

3. **Ensure test is self-contained**:
   - Include all necessary modules in single file
   - Avoid external dependencies unless justified
   - Use `initial` block for stimulus

4. **Test locally before commit**:
   ```bash
   ./scripts/run -b master -t planv_tests/feature_tests/<category>/<test>.sv
   ```

5. **Verify logs**:
   - Check `logs/feature_tests/<category>/<test>.log` for errors
   - Ensure "*-* All Tests Passed *-*" appears in log

**For UVM Tests:**

1. **Create dedicated directory** under `planv_tests/uvm_tests/<test_name>/`

2. **Include custom Makefile** (not auto-generated like feature tests)

3. **Document dependencies** and build instructions in test directory

4. **Note platform limitations** if test cannot run on GitHub Actions

### Modifying Existing Tests

**Before modification:**
- Understand test purpose and expected behavior
- Check if test is actively used in CI/CD
- Review related tests in same category

**During modification:**
- Preserve original test intent
- Update header comments if behavior changes
- Maintain backward compatibility if possible

**After modification:**
- Run full category test suite
- Update documentation if test behavior changed
- Note changes in git commit message

### Handling Test Failures

**When test fails:**

1. **Analyze logs** in `logs/feature_tests/<category>/<test>.log`
   - Look for Verilator compilation errors
   - Check simulation runtime errors
   - Verify solver (z3) issues if constraint-related

2. **Reproduce locally**:
   ```bash
   cd sim/feature_tests/<category>/<test>
   export VERILATOR_ROOT=/path/to/verilator/<branch>
   make clean
   make
   ```

3. **Debug with extra flags** (modify Makefile):
   - `make debug=1` - Enable Verilator debug mode
   - `make json_dump=1` - Dump AST as JSON

4. **Categorize failure**:
   - Verilator bug → Report to Verilator repo
   - PlanV-specific issue → Create issue in this repo
   - Test error → Fix test file

**DO NOT:**
- Create new status subdirectories for failed tests
- Mix test results with source files
- Archive failed tests without documentation

## Test Organization Best Practices

### Recommended Structure Changes (Future)

**Current Issues:**
- Status subdirectories (`passed/`, `failed/`, etc.) create confusion
- Branch-specific result directories mix with source
- Unclear canonical test set

**Proposed Improvement:**

```
planv_tests/feature_tests/<category>/
├── README.md                 # Category documentation
├── t_<feature>_basic.sv      # Active tests (no status subdirs)
├── t_<feature>_edge_case.sv
└── archived/                 # Optional: historical tests
    └── <date>_<reason>/
        └── old_test.sv
```

**Guidelines:**
- Keep all active tests in category root
- Document test purpose in category README.md
- Archive obsolete tests with context (date, reason)
- Store test results in `logs/` or CI artifacts, NOT in source tree
- Use git tags to mark known-good test snapshots

### Test Maintenance

**Regular Tasks:**
- Review and clean up archived tests
- Update category README.md files
- Sync with upstream Verilator changes
- Validate tests against new Verilator versions

**When to Archive Tests:**
- Feature no longer relevant
- Test superseded by better version
- Known-failing test with documented issue

**Documentation Requirements:**
- Explain test purpose in comments
- Document expected behavior
- Note any platform-specific issues
- Reference related Verilator issues/PRs if applicable

## Common Pitfalls & Solutions

### Issue: Test Runs Locally but Fails in CI

**Causes:**
- Missing dependencies in CI environment
- Environment variable differences
- Verilator version mismatch

**Solutions:**
- Check `.github/workflows/PlanV_verilator_feature_tests.yml` for dependencies
- Verify VERILATOR_ROOT is set correctly
- Test with exact CI Verilator version locally

### Issue: Verilator Width Truncation Warnings

**Symptom:**
```
%Warning-WIDTHTRUNC: Operator ASSIGNW expects 8 bits on the Assign RHS, but Assign RHS's CONST generates 32 bits.
```

**Solution:**
```systemverilog
/* verilator lint_off WIDTHTRUNC */
int result = randomize(...);
/* verilator lint_on WIDTHTRUNC */
```

### Issue: Variables Uninitialized in `initial` Block

**Symptom:**
```
%Error: Variable used before initialization
```

**Solution:**
```systemverilog
// Wrong:
initial begin
    int x;
    x = 5;
end

// Correct:
initial begin
    automatic int x = 0;
    x = 5;
end
```

### Issue: Missing Solver Dependency

**Symptom:**
```
No constraint solver installed
```

**Solution:**
```bash
# Install z3-solver
pip3 install z3-solver

# Verify installation
python3 -c "import z3; print(z3.get_version_string())"
```

## External Dependencies

### Verilator Versions
- Managed as git submodules in `verilator/` directory
- Each version in separate subdirectory
- Updated manually by user

### UVM Libraries
- `uvm_lib/uvm-2017/` - IEEE 1800.2-2017 UVM reference
- `uvm_lib/uvm-antmicro-deprecatedApi/` - Deprecated API compatibility

### Python Dependencies
- `z3-solver` - Constraint solver backend
- `jinja2` - HTML report generation
- `pyyaml` - Configuration parsing
- `robotframework` - (optional) Test framework

### Build Tools
- gcc-12 / g++-12 (minimum)
- autoconf, make
- flex, bison
- ccache (for faster builds)

## Project Boundaries

**This Repository:**
- PlanV-specific feature validation tests
- Multi-version Verilator testing infrastructure
- UVM integration examples

**Separate Repository:**
- `/home/yilou/Desktop/OSVISE/planvtech/verilator` - PlanV Verilator development
- Official Verilator repo upstream

**DO NOT:**
- Modify Verilator source in this repo (use dedicated repo)
- Commit build artifacts (`sim/`, `logs/`) to git
- Mix test source with test results

## Quick Reference Commands

### Local Testing
```bash
# Test single category
./scripts/run -b master -t planv_tests/feature_tests/assertions

# Test single file
./scripts/run -b master -t planv_tests/feature_tests/assertions/t_assertion_immediate.sv

# Test with different Verilator branch
./scripts/run -b version-5.044 -t planv_tests/feature_tests/constrained_random

# Clean generated artifacts
rm -rf sim/ logs/
```

### Debugging
```bash
# Manual test execution with debug
cd sim/feature_tests/<category>/<test>
export VERILATOR_ROOT=/path/to/PlanV_Verilator_Feature_Tests/verilator/master
make clean
make debug=1
make json_dump=1  # Dump AST

# Check Verilator version
$VERILATOR_ROOT/bin/verilator --version

# Verify z3 solver
python3 -c "import z3; print(z3.get_version_string())"
```

### Git Workflow
```bash
# Update submodules
git submodule update --init --recursive

# Check status
git status
git branch -a

# Create feature branch
git checkout -b feature/new-test-category

# Commit new test
git add planv_tests/feature_tests/<category>/t_new_test.sv
git commit -m "Add test for <feature>"
```

## Notes

- **Test execution time**: Full suite can take significant time (minutes to hours)
- **CI limitations**: Some UVM tests cannot run on GitHub Actions (resource constraints)
- **Parallel execution**: CI runs each Verilator branch in parallel
- **Log retention**: Logs are uploaded as GitHub Actions artifacts (limited retention)
- **Submodule updates**: Manual process, not automatic
- **Version compatibility**: Tests may behave differently across Verilator versions

## Contact & Support

- **Primary Contact**: yilou.wang@planv.tech
- **Issues**: GitHub Issues in this repository
- **License**: Solderpad Hardware License, Version 2.0
- **Copyright**: PlanV GmbH, 2024. All rights reserved.
