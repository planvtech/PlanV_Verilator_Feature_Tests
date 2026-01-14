// DESCRIPTION: PlanV Verilator Feature Tests - Common Test Utilities
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Contact: yilou.wang@planv.tech
//
// Usage:
//   `include "test_utils.svh"
//
// Compile with +define+DEBUG to enable debug output:
//   vlog +define+DEBUG test.sv
//   verilator +define+DEBUG test.sv

`ifndef TEST_UTILS_SVH
`define TEST_UTILS_SVH

//=============================================================================
// Debug Display Macros
//=============================================================================
// When DEBUG is defined: prints the message
// When DEBUG is not defined: compiles to nothing
`ifdef DEBUG
  `define DBG(msg) $display msg
`else
  `define DBG(msg)
`endif

// Info display - always shown (for important status messages)
`define INFO(msg) $display msg

//=============================================================================
// Test Pass/Fail Macros
//=============================================================================
`define TEST_PASS \
    $write("*-* All Finished *-*\n"); \
    $finish;

`define TEST_FAIL(msg) \
    $write("TEST FAILED: %s", msg); \
    $stop;

//=============================================================================
// Randomization Verification Macros
//=============================================================================
// CHECK_RAND: Verify that a field produces different random values
// Usage: `CHECK_RAND(obj, obj.field)
// Runs 10 randomizations and checks that at least one value differs
`define CHECK_RAND(cl, field) \
begin \
    longint prev_result; \
    int ok = 0; \
    for (int i = 0; i < 10; i++) begin \
        longint result; \
        void'(cl.randomize()); \
        result = longint'(field); \
        if (i > 0 && result != prev_result) ok = 1; \
        prev_result = result; \
    end \
    if (ok != 1) begin \
        $display("Error: Randomization produced same value for field"); \
        $stop; \
    end \
    `DBG(("CHECK_RAND passed for field")) \
end

// CHECK_RAND_WITH_NAME: Same as CHECK_RAND but with custom field name in error message
`define CHECK_RAND_WITH_NAME(cl, field, name) \
begin \
    longint prev_result; \
    int ok = 0; \
    for (int i = 0; i < 10; i++) begin \
        longint result; \
        void'(cl.randomize()); \
        result = longint'(field); \
        if (i > 0 && result != prev_result) ok = 1; \
        prev_result = result; \
    end \
    if (ok != 1) begin \
        $write("Error: Randomization produced same value for %s", name); \
        $stop; \
    end \
    `DBG(("CHECK_RAND passed for %s", name)) \
end

// RAND_OR_FAIL: Call randomize and fail test if it returns 0
`define RAND_OR_FAIL(obj) \
    if (!obj.randomize()) begin \
        $write("Error: randomize() failed for object"); \
        $stop; \
    end

`endif // TEST_UTILS_SVH
