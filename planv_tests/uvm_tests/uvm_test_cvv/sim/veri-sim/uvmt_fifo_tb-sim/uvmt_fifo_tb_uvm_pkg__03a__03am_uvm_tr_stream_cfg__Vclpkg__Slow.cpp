// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg___ctor_var_reset(uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg* vlSelf);

uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg::uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg() = default;
uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg::~uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg() = default;

void uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg::ctor(uvmt_fifo_tb__Syms* symsp, const char* namep) {
    vlSymsp = symsp;
    vlNamep = strdup(Verilated::catName(vlSymsp->name(), namep));
    // Reset structure values
    uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg___ctor_var_reset(this);
}

void uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

void uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg__Vclpkg::dtor() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
