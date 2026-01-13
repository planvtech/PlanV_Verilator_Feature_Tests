// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171__Vclpkg::__VnoInFunc_from_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, CData/*0:0*/ &value, CData/*0:0*/ &from_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171__Vclpkg::__VnoInFunc_from_name\n"); );
    // Body
    if ((0U == this->__PVT__map.size())) {
        this->__VnoInFunc_m_init_map(vlSymsp);
    }
    if (this->__PVT__map.exists(name)) {
        value = this->__PVT__map.at(name);
        from_name__Vfuncrtn = 1U;
    } else {
        from_name__Vfuncrtn = 0U;
    }
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171__Vclpkg::__VnoInFunc_m_init_map(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171__Vclpkg::__VnoInFunc_m_init_map\n"); );
    // Body
    CData/*0:0*/ e;
    e = 0;
    this->__PVT__map.at("WR"s) = 0U;
    this->__PVT__map.at("RD"s) = 1U;
    e = 0U;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171::uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171::to_string_middle\n"); );
    // Body
    std::string out;
    return (out);
}
