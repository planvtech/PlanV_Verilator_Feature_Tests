// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

VL_ATTR_COLD void uvmt_fifo_tb_uvmt_fifo_clk_gen_if___eval_static__TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if(uvmt_fifo_tb_uvmt_fifo_clk_gen_if* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvmt_fifo_clk_gen_if___eval_static__TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.start_clk = 0U;
    vlSelfRef.clk_period = 10.0;
}

VL_ATTR_COLD void uvmt_fifo_tb_uvmt_fifo_clk_gen_if___ctor_var_reset(uvmt_fifo_tb_uvmt_fifo_clk_gen_if* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvmt_fifo_clk_gen_if___ctor_var_reset\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    const uint64_t __VscopeHash = VL_MURMUR64_HASH(vlSelf->vlNamep);
    vlSelf->clk = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 16707436170211756652ull);
    vlSelf->reset_n = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 14129604614540204776ull);
    vlSelf->start_clk = 0;
    vlSelf->clk_period = 0;
    vlSelf->__Vtrigprevexpr_h6568ff79__0 = 0;
    vlSelf->__Vtrigprevexpr_h8ae68869__0 = 0;
    vlSelf->__Vtrigprevexpr_h5029f6a9__0 = 0;
    vlSelf->__Vtrigprevexpr_hd633b7f2__0 = 0;
}
