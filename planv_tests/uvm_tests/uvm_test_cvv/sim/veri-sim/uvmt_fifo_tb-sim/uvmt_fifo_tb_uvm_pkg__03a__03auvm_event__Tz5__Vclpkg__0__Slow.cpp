// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

VL_ATTR_COLD void uvmt_fifo_tb_uvm_pkg__03a__03auvm_event__Tz5__Vclpkg___eval_static__TOP__uvm_pkg__03a__03auvm_event__Tz5__Vclpkg(uvmt_fifo_tb_uvm_pkg__03a__03auvm_event__Tz5__Vclpkg* vlSelf, VlProcessRef vlProcess) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_event__Tz5__Vclpkg___eval_static__TOP__uvm_pkg__03a__03auvm_event__Tz5__Vclpkg\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __Vfunc_m_register_cb__1__Vfuncout;
    __Vfunc_m_register_cb__1__Vfuncout = 0;
    // Body
    vlSelfRef.__VnoInFunc_m_register_cb(vlProcess, vlSymsp, __Vfunc_m_register_cb__1__Vfuncout);
    vlSelfRef.__PVT__m_cb_registered = __Vfunc_m_register_cb__1__Vfuncout;
}

VL_ATTR_COLD void uvmt_fifo_tb_uvm_pkg__03a__03auvm_event__Tz5__Vclpkg___ctor_var_reset(uvmt_fifo_tb_uvm_pkg__03a__03auvm_event__Tz5__Vclpkg* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_event__Tz5__Vclpkg___ctor_var_reset\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelf->__PVT__m_cb_registered = 0;
}
