// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320__Vclpkg::__VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320> &get__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320__Vclpkg::__VnoInFunc_get\n"); );
    // Body
    if ((VlNull{} == this->__PVT__m_b_inst)) {
        this->__PVT__m_b_inst = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320, vlSymsp);
    }
    get__Vfuncrtn = this->__PVT__m_b_inst;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320(uvmt_fifo_tb__Syms* __restrict vlSymsp)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid_base(vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz320::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid_base::to_string_middle();
    return (out);
}
