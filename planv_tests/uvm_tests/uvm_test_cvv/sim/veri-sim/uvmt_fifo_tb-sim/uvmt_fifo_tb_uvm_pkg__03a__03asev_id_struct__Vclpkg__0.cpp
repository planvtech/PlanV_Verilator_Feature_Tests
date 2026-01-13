// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct::uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__sev_specified = 0;
    __PVT__id_specified = 0;
    __PVT__sev = 0;
    __PVT__is_on = 0;
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03asev_id_struct::to_string_middle\n"); );
    // Body
    std::string out;
    out += "sev_specified:" + VL_TO_STRING(__PVT__sev_specified);
    out += ", id_specified:" + VL_TO_STRING(__PVT__id_specified);
    out += ", sev:" + VL_TO_STRING(__PVT__sev);
    out += ", id:" + VL_TO_STRING(__PVT__id);
    out += ", is_on:" + VL_TO_STRING(__PVT__is_on);
    return (out);
}
