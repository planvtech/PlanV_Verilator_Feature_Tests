// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::__VnoInFunc_set(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<uvmt_fifo_tb_uvm_hdl_path_slice__struct__0> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::__VnoInFunc_set\n"); );
    // Body
    this->__PVT__slices = t;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::__VnoInFunc_add_slice(uvmt_fifo_tb__Syms* __restrict vlSymsp, uvmt_fifo_tb_uvm_hdl_path_slice__struct__0 slice) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::__VnoInFunc_add_slice\n"); );
    // Body
    this->__PVT__slices.renew_copy(((IData)(1U) + this->__PVT__slices.size()), this->__PVT__slices);
    this->__PVT__slices.atWrite((this->__PVT__slices.size() 
                                 - (IData)(1U))) = slice;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::__VnoInFunc_add_path(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string path, IData/*31:0*/ offset, IData/*31:0*/ size) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::__VnoInFunc_add_path\n"); );
    // Body
    uvmt_fifo_tb_uvm_hdl_path_slice__struct__0 t;
    t.__PVT__offset = 0;
    t.__PVT__size = 0;
    t.__PVT__offset = offset;
    t.__PVT__path = path;
    t.__PVT__size = size;
    this->__VnoInFunc_add_slice(vlSymsp, t);
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__slices.atDefault().__PVT__offset = 0;
    __PVT__slices.atDefault().__PVT__size = 0;
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat::to_string_middle\n"); );
    // Body
    std::string out;
    out += "slices:" + VL_TO_STRING(__PVT__slices);
    return (out);
}
