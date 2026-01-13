// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb___024root___ctor_var_reset(uvmt_fifo_tb___024root* vlSelf);

uvmt_fifo_tb___024root::uvmt_fifo_tb___024root(uvmt_fifo_tb__Syms* symsp, const char* namep)
    : __VdlySched{*symsp->_vm_contextp__}
 {
    vlSymsp = symsp;
    vlNamep = strdup(namep);
    // Reset structure values
    uvmt_fifo_tb___024root___ctor_var_reset(this);
}

void uvmt_fifo_tb___024root::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

uvmt_fifo_tb___024root::~uvmt_fifo_tb___024root() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
