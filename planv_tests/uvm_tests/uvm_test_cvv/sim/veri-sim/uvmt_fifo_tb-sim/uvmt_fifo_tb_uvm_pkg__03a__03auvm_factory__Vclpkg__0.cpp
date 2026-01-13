// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory__Vclpkg::__VnoInFunc_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory> &get__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory__Vclpkg::__VnoInFunc_get\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__0__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory> __Vtask_get_factory__1__Vfuncout;
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> s;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__0__Vfuncout);
    s = __Vfunc_get__0__Vfuncout;
    VL_NULL_CHECK(s, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_factory.svh", 92)->__VnoInFunc_get_factory(vlSymsp, __Vtask_get_factory__1__Vfuncout);
    get__Vfuncrtn = __Vtask_get_factory__1__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory__Vclpkg::__VnoInFunc_set(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory> f) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory__Vclpkg::__VnoInFunc_set\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__2__Vfuncout;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> s;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__2__Vfuncout);
    s = __Vfunc_get__2__Vfuncout;
    VL_NULL_CHECK(s, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_factory.svh", 99)->__VnoInFunc_set_factory(vlSymsp, f);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_register(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_register\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_inst_override_by_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> original_type, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> override_type, std::string full_inst_path) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_inst_override_by_type\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_inst_override_by_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string original_type_name, std::string override_type_name, std::string full_inst_path) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_inst_override_by_name\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_type_override_by_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> original_type, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> override_type, CData/*0:0*/ replace) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_type_override_by_type\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_type_override_by_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string original_type_name, std::string override_type_name, CData/*0:0*/ replace) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_type_override_by_name\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_create_object_by_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> requested_type, std::string parent_inst_path, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create_object_by_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_create_object_by_type\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_create_component_by_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> requested_type, std::string parent_inst_path, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> &create_component_by_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_create_component_by_type\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_create_object_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string requested_type_name, std::string parent_inst_path, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create_object_by_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_create_object_by_name\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_is_type_name_registered(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string type_name, CData/*0:0*/ &is_type_name_registered__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_is_type_name_registered\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_is_type_registered(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> obj, CData/*0:0*/ &is_type_registered__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_is_type_registered\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_create_component_by_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string requested_type_name, std::string parent_inst_path, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> &create_component_by_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_create_component_by_name\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_type_alias(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string alias_type_name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> original_type) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_type_alias\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_inst_alias(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string alias_type_name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> original_type, std::string full_inst_path) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_set_inst_alias\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_debug_create_by_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> requested_type, std::string parent_inst_path, std::string name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_debug_create_by_type\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_debug_create_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string requested_type_name, std::string parent_inst_path, std::string name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_debug_create_by_name\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_find_override_by_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> requested_type, std::string full_inst_path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &find_override_by_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_find_override_by_type\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_find_override_by_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string requested_type_name, std::string full_inst_path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &find_override_by_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_find_override_by_name\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_find_wrapper_by_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string type_name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &find_wrapper_by_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_find_wrapper_by_name\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_print(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ all_types) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::__VnoInFunc_print\n"); );
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory::to_string_middle\n"); );
    // Body
    std::string out;
    return (out);
}
