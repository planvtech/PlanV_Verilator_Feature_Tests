# Scripts

## Verilator Testing

| Script | Description |
|--------|-------------|
| `run` | Local test runner for Verilator |
| `ciSystemRunner.sh` | CI runner for GitHub Actions |
| `set_build_run_functions` | Shared functions for setup/build/run |
| `setup_framework` | Simulation directory setup |
| `polish_to_html.py` | Convert logs to HTML reports |

## QuestaSim Validation

| Script | Description |
|--------|-------------|
| `run_questa_batch.sh` | Run all feature tests with QuestaSim |
| `run_questa_pilot.sh` | Run a single directory with QuestaSim |

### Usage

```bash
# Run all tests
./scripts/run_questa_batch.sh

# Run single directory
./scripts/run_questa_pilot.sh 18_randomization/constraint_blocks
```

### Negative Tests

Tests in `/invalid/` directories or with `// TEST_NEGATIVE:` comment are expected to fail compilation. These are marked as `[XFAIL]` in test results.
