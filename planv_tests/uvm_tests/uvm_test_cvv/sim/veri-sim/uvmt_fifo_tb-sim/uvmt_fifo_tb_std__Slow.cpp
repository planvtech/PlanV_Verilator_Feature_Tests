// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_std___ctor_var_reset(uvmt_fifo_tb_std* vlSelf);

uvmt_fifo_tb_std::uvmt_fifo_tb_std() = default;
uvmt_fifo_tb_std::~uvmt_fifo_tb_std() = default;

void uvmt_fifo_tb_std::ctor(uvmt_fifo_tb__Syms* symsp, const char* namep) {
    vlSymsp = symsp;
    vlNamep = strdup(Verilated::catName(vlSymsp->name(), namep));
    // Reset structure values
    uvmt_fifo_tb_std___ctor_var_reset(this);
}

void uvmt_fifo_tb_std::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

void uvmt_fifo_tb_std::dtor() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
