// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator__Vclpkg::__VnoInFunc_create_by_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> obj_wrpr, std::string contxt, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> unused, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create_by_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator__Vclpkg::__VnoInFunc_create_by_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__0__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory> __Vtask_get_factory__1__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_create_object_by_type__2__Vfuncout;
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> cs;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory> factory;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__0__Vfuncout);
    cs = __Vfunc_get__0__Vfuncout;
    VL_NULL_CHECK(cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_registry.svh", 670)->__VnoInFunc_get_factory(vlSymsp, __Vtask_get_factory__1__Vfuncout);
    factory = __Vtask_get_factory__1__Vfuncout;
    VL_NULL_CHECK(factory, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_registry.svh", 672)->__VnoInFunc_create_object_by_type(vlProcess, vlSymsp, obj_wrpr, contxt, name, __Vtask_create_object_by_type__2__Vfuncout);
    create_by_type__Vfuncrtn = __Vtask_create_object_by_type__2__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator__Vclpkg::__VnoInFunc_base_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &base_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator__Vclpkg::__VnoInFunc_base_type_name\n"); );
    // Body
    base_type_name__Vfuncrtn = "object"s;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator::uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_registry_object_creator::to_string_middle\n"); );
    // Body
    std::string out;
    return (out);
}
