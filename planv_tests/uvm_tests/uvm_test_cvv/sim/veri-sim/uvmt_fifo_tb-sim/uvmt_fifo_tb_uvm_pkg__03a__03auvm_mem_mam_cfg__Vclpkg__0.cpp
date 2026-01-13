// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg::uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__n_bytes = 0;
    __PVT__start_offset = 0;
    __PVT__end_offset = 0;
    __PVT__mode = 0;
    __PVT__locality = 0;
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg::to_string_middle\n"); );
    // Body
    std::string out;
    out += "n_bytes:" + VL_TO_STRING(__PVT__n_bytes);
    out += ", start_offset:" + VL_TO_STRING(__PVT__start_offset);
    out += ", end_offset:" + VL_TO_STRING(__PVT__end_offset);
    out += ", mode:" + VL_TO_STRING(__PVT__mode);
    out += ", locality:" + VL_TO_STRING(__PVT__locality);
    return (out);
}
