// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::__VnoInFunc_create_object(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create_object__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::__VnoInFunc_create_object\n"); );
    // Body
    create_object__Vfuncrtn = VlNull{};
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::__VnoInFunc_create_component(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> &create_component__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::__VnoInFunc_create_component\n"); );
    // Body
    create_component__Vfuncrtn = VlNull{};
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::__VnoInFunc_get_type_name\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::__VnoInFunc_initialize(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::__VnoInFunc_initialize\n"); );
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::to_string_middle\n"); );
    // Body
    std::string out;
    return (out);
}
