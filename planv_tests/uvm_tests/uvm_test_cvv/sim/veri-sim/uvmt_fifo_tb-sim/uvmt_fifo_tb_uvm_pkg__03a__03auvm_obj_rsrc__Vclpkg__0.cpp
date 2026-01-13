// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, std::string s)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz76(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::new\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool> __Vfunc_get__1__Vfuncout;
    // Body
    _ctor_var_reset(vlSymsp);
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool> rp;
    ;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_resource_pool__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__1__Vfuncout);
    rp = __Vfunc_get__1__Vfuncout;
    VL_NULL_CHECK(rp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_resource_specializations.svh", 134)->__VnoInFunc_set_scope(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc>{this}, s);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__4__Vfuncout;
    __Vfunc___VBasicRand__4__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__4__Vfuncout);
            }(), __Vfunc___VBasicRand__4__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_obj_rsrc::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz76::to_string_middle();
    return (out);
}
