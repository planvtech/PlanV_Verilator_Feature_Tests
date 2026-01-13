// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Implementation of DPI export functions
//
// Verilator compiles this file in when DPI functions are used.
// If you have multiple Verilated designs with the same DPI exported
// function names, you will get multiple definition link errors from here.
// This is an unfortunate result of the DPI specification.
// To solve this, either
//    1. Call uvmt_fifo_tb::{export_function} instead,
//       and do not even bother to compile this file
// or 2. Compile all __Dpi.cpp files in the same compiler run,
//       and #ifdefs already inserted here will sort everything out.

#include "uvmt_fifo_tb__Dpi.h"
#include "uvmt_fifo_tb.h"

#ifndef VL_DPIDECL_m__uvm_report_dpi_
#define VL_DPIDECL_m__uvm_report_dpi_
void m__uvm_report_dpi(int severity, const char* id, const char* message, int verbosity, const char* filename, int line) {
    // DPI export at /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh:114:15
    return uvmt_fifo_tb::m__uvm_report_dpi(severity, id, message, verbosity, filename, line);
}
#endif

