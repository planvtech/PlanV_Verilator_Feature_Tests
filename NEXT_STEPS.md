# Next Steps for Randomization Tests Refactoring

## What's Been Done ✅

1. **Analyzed IEEE 1800-2023 Chapter 18** structure
2. **Designed new directory structure** based on IEEE sections
3. **Created enhanced naming convention** with optional subcategory field
4. **Analyzed all 126 randomization tests**:
   - Identified unclear filenames (`t_1.sv`, `t_2.sv`, etc.)
   - Read content to understand purpose
   - Mapped to appropriate new locations
5. **Created migration mapping** (MIGRATION_MAP.csv) for all files
6. **Created new directory structure** with all subdirectories
7. **Generated README documentation** for main categories
8. **Created automation scripts**:
   - `migrate_randomization_tests.sh` - Automated migration
   - `detect_duplicates.sh` - Duplicate detection

## Files Created

```
PlanV_Verilator_Feature_Tests/
├── RANDOMIZATION_REFACTOR.md           # Detailed refactoring plan
├── MIGRATION_MAP.csv                   # File-by-file migration mapping
├── NEXT_STEPS.md                       # This file
├── scripts/
│   ├── migrate_randomization_tests.sh  # Migration automation
│   └── detect_duplicates.sh            # Duplicate detection
└── planv_tests/feature_tests/
    ├── randomization/                  # New structure (empty, ready)
    │   ├── README.md                   # Main documentation
    │   ├── rand_variables/
    │   │   └── README.md
    │   ├── constraint_blocks/
    │   │   └── README.md
    │   ├── std_randomize/
    │   │   └── README.md
    │   ├── special_cases/
    │   │   └── README.md
    │   └── ... (all other subdirs)
    └── _archived/
        └── 20250112_pre_refactor/      # Archive location (empty)
```

## What to Do Next

### Immediate (Before Migration)

#### 1. Review and Approve Plan (5-10 min)
- Read `RANDOMIZATION_REFACTOR.md` - detailed plan
- Check `MIGRATION_MAP.csv` - verify file mappings make sense
- Confirm naming convention is acceptable

#### 2. Detect Duplicates (10-15 min)
```bash
cd /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests
chmod +x scripts/detect_duplicates.sh
./scripts/detect_duplicates.sh
# Review the generated DUPLICATE_REPORT_*.md
```

**Purpose**: Identify files that exist in multiple locations (e.g., `passed/`, `to_test/`, `master/`)

**Action**: Decide which version to keep, update MIGRATION_MAP.csv

#### 3. Test Dry Run (5 min)
```bash
chmod +x scripts/migrate_randomization_tests.sh
./scripts/migrate_randomization_tests.sh --dry-run | head -50
```

**Purpose**: Verify migration script logic without modifying files

**Action**: Check if output looks reasonable

### Migration Execution (30-60 min)

#### 4. Create Git Safety Net
```bash
cd /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests
git add .
git commit -m "Add randomization refactor plan and scripts"
git tag refactor-randomization-before
```

#### 5. Run Duplicate Detection and Update Map
```bash
./scripts/detect_duplicates.sh
# Review DUPLICATE_REPORT_*.md
# Update MIGRATION_MAP.csv based on findings
```

#### 6. Run Migration (First Phase)
```bash
# Migrate high-priority files first (issue reproductions, clear renames)
# You may want to edit the script to only process HIGH priority items first
./scripts/migrate_randomization_tests.sh

# Review migration log
cat MIGRATION_LOG_*.txt
```

#### 7. Verify Migration
```bash
# Check new structure
tree planv_tests/feature_tests/randomization/ | head -100

# Verify files were migrated
ls -la planv_tests/feature_tests/randomization/constraint_blocks/global/

# Check archived files
ls -la _archived/20250112_pre_refactor/
```

#### 8. Test Migrated Files
```bash
# Run a sample of migrated tests
./scripts/run -b master -t planv_tests/feature_tests/randomization/constraint_blocks/global/t_constraint_global_array_selection.sv

# Or run all migrated tests (may take time)
./scripts/run -b master -t planv_tests/feature_tests/randomization/constraint_blocks/global/
```

### Post-Migration (1-2 hours)

#### 9. Handle Status Subdirectories
After main migration, process status subdirectories:

```bash
# List all status subdirs
find planv_tests/feature_tests/constrained_random -type d | grep -E "(passed|failed|to_test|modify)"

# For each status subdir:
# 1. Compare files with already-migrated versions
# 2. If identical -> archive
# 3. If different -> determine which is correct, migrate unique tests
# 4. Archive the entire status subdir when done
```

Example workflow:
```bash
# Compare passed/ version with already-migrated version
diff planv_tests/feature_tests/constrained_random/constraint_global/passed/t_global_rand_t1.sv \
     planv_tests/feature_tests/randomization/constraint_blocks/global/t_constraint_global_basic.sv

# If different, investigate which to keep
# Update MIGRATION_MAP.csv if needed
```

#### 10. Archive Old Structure
```bash
# Move entire old structure to archive
mv planv_tests/feature_tests/constrained_random/* \
   planv_tests/feature_tests/_archived/20250112_pre_refactor/constrained_random/

# Keep a record
echo "Archived on $(date)" > planv_tests/feature_tests/_archived/20250112_pre_refactor/ARCHIVE_INFO.txt
```

#### 11. Final Validation
```bash
# Run ALL randomization tests in new location
./scripts/run -b master -t planv_tests/feature_tests/randomization

# Compare results with baseline (if you have one)
# Document any test failures
```

#### 12. Update Documentation
- [ ] Update project README to reflect new structure
- [ ] Update `.claude/CLAUDE.md` test structure section
- [ ] Create MIGRATION_HISTORY.md documenting what was done

### Commit and Review (30 min)

#### 13. Commit Changes
```bash
git add .
git status  # Review what's being committed
git commit -m "Refactor: Reorganize randomization tests following IEEE 1800-2023 structure

- Created new directory structure based on IEEE Chapter 18 sections
- Renamed unclear files (t_1.sv -> t_constraint_global_nested_membersel.sv, etc.)
- Moved issue reproductions to special_cases/issue_reproductions/
- Archived old structure to _archived/20250112_pre_refactor/
- Created comprehensive README documentation for all categories

Total files migrated: XXX
Files renamed: XXX
See MIGRATION_MAP.csv for complete mapping"

git tag refactor-randomization-complete
```

#### 14. Create Summary Report
Generate a final report documenting:
- Number of files migrated
- Files renamed (before/after)
- Any issues encountered
- Test results before/after
- Lessons learned

## Manual Tasks (Cannot Be Automated)

### High Priority
1. **Duplicate resolution** - Decide which version to keep when duplicates exist
2. **Failed test analysis** - Determine if tests in `*_failed/` are:
   - Known Verilator bugs → document in README
   - Invalid tests → archive
   - Should pass → investigate and fix

### Medium Priority
3. **Test validation** - Run tests in `to_test/` to verify they work
4. **Module name verification** - Ensure all module names match filenames after migration

### Low Priority
5. **README enhancement** - Add more examples to category READMEs
6. **Test consolidation** - Merge similar tests if appropriate (e.g., `t_foo_v1.sv`, `t_foo_v2.sv` → `t_foo_comprehensive.sv`)

## Decision Points

Before proceeding, confirm:

1. **Naming convention approved?**
   - Current: `t_<category>_<subcategory>_<feature>_<variant>.sv`
   - Alternative: Simpler `t_<category>_<feature>.sv`?

2. **Duplicate handling strategy?**
   - Keep most recent?
   - Keep most comprehensive?
   - Keep from master branch results?

3. **Failed test policy?**
   - Move to special_cases/known_failures/?
   - Archive immediately?
   - Investigate first?

4. **Status subdir priority?**
   - Migrate passed/ first?
   - Archive all status subdirs immediately?
   - Process selectively?

## Timeline Estimate

| Phase | Task | Time |
|-------|------|------|
| Pre-Migration | Review, duplicate detection, decisions | 1-2 hours |
| Migration | Run scripts, verify results | 1-2 hours |
| Post-Migration | Status subdirs, testing, cleanup | 2-3 hours |
| Documentation | Update docs, commit, report | 1 hour |
| **Total** | | **5-8 hours** |

Can be done in:
- **Fast track**: 1 day (focus on high-priority files only)
- **Thorough**: 2-3 days (includes full validation and duplicate analysis)

## Rollback Plan

If something goes wrong:

```bash
# Immediate rollback
git reset --hard refactor-randomization-before
git tag -d refactor-randomization-complete  # if created

# Or restore from archive
rm -rf planv_tests/feature_tests/randomization
mv planv_tests/feature_tests/_archived/20250112_pre_refactor/constrained_random \
   planv_tests/feature_tests/constrained_random
```

## Questions to Answer

Before starting migration:

1. Should we process all files at once, or migrate in batches (e.g., by category)?
2. Do we want to run tests before AND after migration to compare results?
3. Should failed tests be migrated or archived immediately?
4. What to do with `vsim_falied/` (note the typo in original dirname)?
5. Keep or discard branch-specific test result directories (`9_19/`, `master/`)?

## Support Files

All necessary files are ready:
- ✅ MIGRATION_MAP.csv - Complete mapping
- ✅ RANDOMIZATION_REFACTOR.md - Detailed plan
- ✅ migrate_randomization_tests.sh - Automation script
- ✅ detect_duplicates.sh - Duplicate finder
- ✅ README.md templates - Documentation

## Let's Start!

**Recommended first step:**

```bash
cd /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests
./scripts/detect_duplicates.sh
```

Review the duplicate report, then we can proceed with migration!
