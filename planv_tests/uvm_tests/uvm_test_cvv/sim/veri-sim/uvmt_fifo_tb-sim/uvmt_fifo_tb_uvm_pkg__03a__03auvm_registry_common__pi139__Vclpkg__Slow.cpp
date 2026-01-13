// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg___ctor_var_reset(uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg* vlSelf);

uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg::uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg() = default;
uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg() = default;

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg::ctor(uvmt_fifo_tb__Syms* symsp, const char* namep) {
    vlSymsp = symsp;
    vlNamep = strdup(Verilated::catName(vlSymsp->name(), namep));
    // Reset structure values
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg___ctor_var_reset(this);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi139__Vclpkg::dtor() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
