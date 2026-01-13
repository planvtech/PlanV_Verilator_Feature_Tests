// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6::uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6::to_string_middle\n"); );
    // Body
    std::string out;
    out += "wr_seq:" + VL_TO_STRING(__PVT__wr_seq);
    out += ", wr_sqr:" + VL_TO_STRING(__PVT__wr_sqr);
    out += ", rd_seq:" + VL_TO_STRING(__PVT__rd_seq);
    out += ", rd_sqr:" + VL_TO_STRING(__PVT__rd_sqr);
    return (out);
}
