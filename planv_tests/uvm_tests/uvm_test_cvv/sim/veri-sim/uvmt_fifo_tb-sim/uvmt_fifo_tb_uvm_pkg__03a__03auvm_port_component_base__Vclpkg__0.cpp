// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_component(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_get_connected_to(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base>> &list) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_get_connected_to\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_is_port(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_port__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_is_port\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_is_export(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_export__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_is_export\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_is_imp(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_imp__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_is_imp\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_use_automatic_config(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &use_automatic_config__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_use_automatic_config\n"); );
    // Body
    use_automatic_config__Vfuncrtn = 0U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_do_task_phase(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_do_task_phase\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__2__Vfuncout;
    __Vfunc___VBasicRand__2__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__2__Vfuncout);
            }(), __Vfunc___VBasicRand__2__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::to_string_middle();
    return (out);
}
