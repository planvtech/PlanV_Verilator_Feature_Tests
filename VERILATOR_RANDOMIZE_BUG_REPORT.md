# Verilator Randomize Bug Report

## Summary
When calling `this.randomize()` in UVM test classes, Verilator generates **stub functions** (`__VStdrand_*`) that only return 1 without solving constraints, instead of calling the real `__VnoInFunc_randomize()` function that performs constraint solving.

## Environment
- **Verilator Version**: [Your version]
- **Test Case**: UVM testbench with constrained random objects

## Problem Description

### Observed Behavior
1. `this.randomize()` returns success (1), but **constraints are NOT applied**
2. Variables retain their default values (e.g., `enabled=0` instead of constraint `enabled==1`)
3. Generated C++ code contains:
   - ✅ Correct `__VnoInFunc_randomize()` with `constraint.next(__Vm_rng)`
   - ❌ Stub `__VStdrand_h8a684de2__*()` that only returns 1
   - ❌ All call sites invoke the **stub** instead of the real function

### Root Cause
Verilator incorrectly generates a `VlStdRandomizer __PVT__stdrand;` member in UVM test classes and creates stub wrappers for `randomize()` calls.

## Reproduction

### Test Case 1: Normal Class (✅ Works)
```systemverilog
class test_object_c;
    rand bit [7:0] value;
    constraint value_con {
        value > 10;
        value < 20;
    }
endclass

test_object_c obj = new();
if (!obj.randomize()) $fatal("Failed");
// Result: value is between 11-19 ✅
```

**Generated C++**: Correctly calls `__VnoInFunc_randomize()` ✅

### Test Case 2: UVM Test Class (❌ Fails)
```systemverilog
class config_c;
    rand bit enabled;
    constraint defaults { enabled == 1; }
endclass

class my_test extends uvm_test;
    rand config_c cfg;
    `uvm_component_utils(my_test)

    constraint cfg_con { cfg.enabled == 1; }

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg = config_c::type_id::create("cfg");
        if (!this.randomize()) $fatal("Randomize failed");
        // BUG: cfg.enabled = 0 (default) instead of 1 ❌
    endfunction
endclass
```

**Generated C++ Header**:
```cpp
class my_test : public uvm_test {
public:
    VlStdRandomizer __PVT__stdrand;  // ❌ Should not exist
    VlClassRef<config_c> __PVT__cfg;

    // ✅ Correct implementation exists but is NEVER called
    virtual void __VnoInFunc_randomize(..., IData& randomize__Vfuncrtn);

    // ❌ Stub that gets called instead
    void __VnoInFunc___VStdrand_h8a684de2__0(..., IData& __VStdrand__Vfuncrtn);
};
```

**Generated C++ Implementation**:
```cpp
// ✅ Real randomize (NEVER CALLED)
void my_test::__VnoInFunc_randomize(..., IData& randomize__Vfuncrtn) {
    this->__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = this->__PVT__constraint.next(__Vm_rng);  // ✅ Correct!
}

// ❌ Stub (ACTUALLY CALLED)
void my_test::__VnoInFunc___VStdrand_h8a684de2__0(..., IData& __VStdrand__Vfuncrtn) {
    __VStdrand__Vfuncrtn = 1U;  // ❌ Just returns 1, no constraint solving!
}

// ❌ build_phase calls the stub
void my_test::__VnoInFunc_build_phase(...) {
    // ...
    this->__VnoInFunc___VStdrand_h8a684de2__0(vlSymsp, __Vfunc__Vfuncout);  // ❌ Wrong!
    // Should call: this->__VnoInFunc_randomize(vlSymsp, __Vfunc__Vfuncout);  // ✅
}
```

## Analysis

### Affected Classes
- ❌ Classes inheriting from `uvm_test` / `uvm_component`
- ❌ Any UVM framework class using `uvm_component_utils` macro
- ✅ Normal classes work correctly
- ✅ Classes inheriting from virtual base classes work correctly

### Why `VlStdRandomizer` is Generated
The `VlStdRandomizer` type is meant for SystemVerilog's `std::randomize()` function (randomizing local variables), NOT for class method `this.randomize()`.

Hypothesis: Verilator's parser/elaborator incorrectly classifies `this.randomize()` calls in UVM components as needing `std::randomize()` support, possibly due to:
1. UVM macro expansion patterns
2. Virtual class inheritance detection logic
3. Special handling of `uvm_component` classes

## Expected Behavior
When `this.randomize()` is called, Verilator should:
1. NOT generate `VlStdRandomizer __PVT__stdrand` member
2. NOT generate `__VStdrand_*` stub functions
3. Directly call `__VnoInFunc_randomize()` which performs constraint solving

## Workaround
Currently NO working workaround for UVM test classes. Attempted solutions:
- ❌ Creating objects in constructor (still fails - constraints not applied)
- ❌ Adding delays after randomize (functions cannot have timing)
- ❌ Converting to task (changes UVM phase signature)
- ❌ Manual constraint assignment (defeats purpose of constrained randomization)

## Test Files

### Working Test Case
- Path: `PlanV_Verilator_Feature_Tests/planv_tests/feature_tests/constrained_random/t_fuxian.sv`
- Classes: `test_object_c`, `test_component_c` (with virtual base), `test_with_config_c` (nested objects)
- Result: All classes correctly call `__VnoInFunc_randomize()` ✅

### Failing Test Case
- Path: `PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh`
- Class: `uvmt_fifo_base_test_c extends uvm_test`
- Lines: 101 (build_phase), 188 (randomize_test function)
- Result: Both calls use stub `__VStdrand_*` ❌

### Generated C++ Evidence
- Failing: `uvmt_fifo_tb-sim/uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg.h`
  - Line 58: `VlStdRandomizer __PVT__stdrand;` ❌
  - Line 68-69: Stub declarations `__VStdrand_h8a684de2__*` ❌
  - Line 82: Unused `__VnoInFunc_randomize` ✅ (correct but never called)

- Failing: `uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg__0.cpp`
  - Lines 119, 273: Calls to stub functions ❌
  - Lines 364-376: Real randomize implementation (never called) ✅
  - Lines 391-395, 407-410: Stub implementations ❌

- Working: `t_fuxian-sim/t_fuxian_t_fuxian__03a__03atest_component_c__Vclpkg__0.cpp`
  - No `VlStdRandomizer` member ✅
  - No stub functions ✅
  - Direct calls to `__VnoInFunc_randomize()` ✅

## Impact
This bug makes UVM testbenches with constrained random testing **completely broken** in Verilator, as test configuration objects cannot be randomized properly.

## Requested Fix
Verilator should detect that `this.randomize()` in UVM component classes requires constraint solving and generate appropriate call sites to `__VnoInFunc_randomize()` instead of creating/calling `__VStdrand` stubs.

---

**Attached Files:**
- Test case: `t_fuxian.sv` (working normal classes)
- UVM test: `uvmt_fifo_base_test.svh` (failing UVM test)
- Generated C++: See paths above
- Simulation logs: `veri-sim/simulate.log` vs `vsim-sim/simulate.log`
