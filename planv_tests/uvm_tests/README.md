# UVM Tests

UVM testbenches for validating Verilator's UVM support.

## Test Categories

| Directory | Description | Status |
|-----------|-------------|--------|
| `DUT/` | Shared async FIFO design | ✓ Ready |
| `GettingVerilatorStartedWithUVM/` | Complete UVM env (Vanessa Cooper's book) | ⚠ Partial |
| `uvm_test_1/` | Basic FIFO UVM verification | ✓ Ready |
| `uvm_test_2/` | Extended UVM scenarios | ⚠ Partial |
| `uvm_test_cvv/` | Core-V-Verif style testbench | ⚠ Dev |
| `pyuvm_test/` | Python UVM with cocotb | ✓ Ready |

## Quick Start

```bash
# Simple DUT test (no UVM)
cd DUT && make simulate

# UVM test
cd uvm_test_1/verilator_sim && make simulate UVM_TEST=case0_test

# pyuvm test
cd pyuvm_test && make SIM=verilator
```

## UVM Libraries

Located in `../../uvm_lib/`:
- `uvm-2017/` - IEEE 1800.2-2017
- `uvm-antmicro-deprecatedApi/` - Deprecated API support

## Notes

- Use `-DUVM_NO_DPI` flag (DPI not fully supported)
- Use `--timing` for delay constructs
- See `.claude/UVM_TESTS_OVERVIEW.md` for detailed documentation
