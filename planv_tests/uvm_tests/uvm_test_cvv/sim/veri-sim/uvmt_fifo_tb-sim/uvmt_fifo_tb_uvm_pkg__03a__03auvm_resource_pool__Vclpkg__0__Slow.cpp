// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

VL_ATTR_COLD void uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg___eval_static__TOP__uvm_pkg__03a__03auvm_resource_pool__Vclpkg(uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg* vlSelf, VlProcessRef vlProcess) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg___eval_static__TOP__uvm_pkg__03a__03auvm_resource_pool__Vclpkg\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.__PVT__print_resources__Vstatic__printer 
        = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_tree_printer, vlProcess, vlSymsp, ""s);
}

VL_ATTR_COLD void uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg___ctor_var_reset(uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg___ctor_var_reset\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelf->__PVT__ri_tab.atDefault().__PVT__precedence = 0;
}
