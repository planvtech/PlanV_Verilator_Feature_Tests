// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

VL_ATTR_COLD void uvmt_fifo_tb_uvma_wr_if___ctor_var_reset(uvmt_fifo_tb_uvma_wr_if* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                              uvmt_fifo_tb_uvma_wr_if___ctor_var_reset\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    const uint64_t __VscopeHash = VL_MURMUR64_HASH(vlSelf->vlNamep);
    vlSelf->clk = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 16707436170211756652ull);
    vlSelf->reset_n = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 14129604614540204776ull);
    vlSelf->data = VL_SCOPED_RAND_RESET_I(8, __VscopeHash, 10363016170300574568ull);
    vlSelf->en = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 7710216835639188562ull);
    vlSelf->full = VL_SCOPED_RAND_RESET_I(1, __VscopeHash, 6695099141381822181ull);
}
