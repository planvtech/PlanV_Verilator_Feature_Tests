// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

VL_ATTR_COLD void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg___eval_static__TOP__uvm_pkg__03a__03auvm_vreg__Vclpkg(uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg* vlSelf, VlProcessRef vlProcess) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg___eval_static__TOP__uvm_pkg__03a__03auvm_vreg__Vclpkg\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __Vfunc_m_register_pair__0__Vfuncout;
    __Vfunc_m_register_pair__0__Vfuncout = 0;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_callbacks__Tz329_TBz330__Vclpkg.__VnoInFunc_m_register_pair(vlProcess, vlSymsp, "uvm_vreg"s, "uvm_vreg_cbs"s, __Vfunc_m_register_pair__0__Vfuncout);
    vlSelfRef.__PVT__m_register_cb_uvm_vreg_cbs = __Vfunc_m_register_pair__0__Vfuncout;
}

VL_ATTR_COLD void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg___ctor_var_reset(uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg___ctor_var_reset\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelf->__PVT__m_register_cb_uvm_vreg_cbs = 0;
}
