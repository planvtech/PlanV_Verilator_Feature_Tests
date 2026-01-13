// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_abstract_object_registry__pi199> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_abstract_object_registry__pi199> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_abstract_object_registry__pi199__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvm_vreg_field_cbs"s;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_abstract_object_registry__pi199> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_abstract_object_registry__pi199__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_vreg_field_cbs"s;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_pre_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field> field, QData/*63:0*/ idx, QData/*63:0*/ &wdat, IData/*31:0*/ &path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> &map) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_pre_write\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_post_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field> field, QData/*63:0*/ idx, QData/*63:0*/ wdat, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, IData/*31:0*/ &status) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_post_write\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_pre_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field> field, QData/*63:0*/ idx, IData/*31:0*/ &path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> &map) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_pre_read\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_post_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field> field, QData/*63:0*/ idx, QData/*63:0*/ &rdat, IData/*31:0*/ &path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> &map, IData/*31:0*/ &status) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_post_read\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__3__Vfuncout;
    __Vfunc___VBasicRand__3__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__3__Vfuncout);
            }(), __Vfunc___VBasicRand__3__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__lineno = 0;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs::to_string_middle\n"); );
    // Body
    std::string out;
    out += "fname:" + VL_TO_STRING(__PVT__fname);
    out += ", lineno:" + VL_TO_STRING(__PVT__lineno);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback::to_string_middle();
    return (out);
}
