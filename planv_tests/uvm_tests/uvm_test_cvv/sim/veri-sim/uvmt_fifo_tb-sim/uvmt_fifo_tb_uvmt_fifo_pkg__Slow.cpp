// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvmt_fifo_pkg___ctor_var_reset(uvmt_fifo_tb_uvmt_fifo_pkg* vlSelf);

uvmt_fifo_tb_uvmt_fifo_pkg::uvmt_fifo_tb_uvmt_fifo_pkg() = default;
uvmt_fifo_tb_uvmt_fifo_pkg::~uvmt_fifo_tb_uvmt_fifo_pkg() = default;

void uvmt_fifo_tb_uvmt_fifo_pkg::ctor(uvmt_fifo_tb__Syms* symsp, const char* namep) {
    vlSymsp = symsp;
    vlNamep = strdup(Verilated::catName(vlSymsp->name(), namep));
    // Reset structure values
    uvmt_fifo_tb_uvmt_fifo_pkg___ctor_var_reset(this);
}

void uvmt_fifo_tb_uvmt_fifo_pkg::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

void uvmt_fifo_tb_uvmt_fifo_pkg::dtor() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
