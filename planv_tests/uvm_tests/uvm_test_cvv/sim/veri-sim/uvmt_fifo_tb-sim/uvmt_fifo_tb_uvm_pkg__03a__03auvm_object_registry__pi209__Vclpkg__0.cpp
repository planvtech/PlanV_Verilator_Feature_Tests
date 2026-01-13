// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_type_name\n"); );
    // Locals
    std::string __Vfunc_type_name__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_registry_common__pi230__Vclpkg.__VnoInFunc_type_name(vlSymsp, __Vfunc_type_name__0__Vfuncout);
    type_name__Vfuncrtn = __Vfunc_type_name__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209> &get__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_get\n"); );
    // Body
    if ((VlNull{} == this->__PVT__get__Vstatic__m_inst)) {
        this->__PVT__get__Vstatic__m_inst = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209, vlSymsp);
    }
    get__Vfuncrtn = this->__PVT__get__Vstatic__m_inst;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_create(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent, std::string contxt, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_parent_child_link> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_create\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_parent_child_link> __Vfunc_create__2__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_registry_common__pi230__Vclpkg.__VnoInFunc_create(vlSymsp, name, parent, contxt, __Vfunc_create__2__Vfuncout);
    create__Vfuncrtn = __Vfunc_create__2__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_set_type_override(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> override_type, CData/*0:0*/ replace) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_set_type_override\n"); );
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_registry_common__pi230__Vclpkg.__VnoInFunc_set_type_override(vlSymsp, override_type, replace);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_set_inst_override(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> override_type, std::string inst_path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_set_inst_override\n"); );
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_registry_common__pi230__Vclpkg.__VnoInFunc_set_inst_override(vlSymsp, override_type, inst_path, parent);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_set_type_alias(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string alias_name, CData/*0:0*/ &set_type_alias__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209__Vclpkg::__VnoInFunc_set_type_alias\n"); );
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_registry_common__pi230__Vclpkg.__VnoInFunc_set_type_alias(vlSymsp, alias_name);
    set_type_alias__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::__VnoInFunc_create_object(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create_object__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::__VnoInFunc_create_object\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_parent_child_link> obj;
    obj = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_parent_child_link, vlProcess, vlSymsp, "unnamed-uvm_parent_child_link"s)
            : VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_parent_child_link, vlProcess, vlSymsp, name));
    create_object__Vfuncrtn = obj;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::__VnoInFunc_get_type_name\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi230> __Vfunc_get__2__Vfuncout;
    std::string __Vtask_get_type_name__3__Vfuncout;
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi230> common;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_registry_common__pi230__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__2__Vfuncout);
    common = __Vfunc_get__2__Vfuncout;
    VL_NULL_CHECK(common, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_registry.svh", 200)->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__3__Vfuncout);
    get_type_name__Vfuncrtn = __Vtask_get_type_name__3__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::__VnoInFunc_initialize(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::__VnoInFunc_initialize\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi230> __Vfunc_get__4__Vfuncout;
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_common__pi230> common;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_registry_common__pi230__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__4__Vfuncout);
    common = __Vfunc_get__4__Vfuncout;
    VL_NULL_CHECK(common, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_registry.svh", 281)->__VnoInFunc_initialize(vlProcess, vlSymsp);
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209(uvmt_fifo_tb__Syms* __restrict vlSymsp)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper(vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi209::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper::to_string_middle();
    return (out);
}
