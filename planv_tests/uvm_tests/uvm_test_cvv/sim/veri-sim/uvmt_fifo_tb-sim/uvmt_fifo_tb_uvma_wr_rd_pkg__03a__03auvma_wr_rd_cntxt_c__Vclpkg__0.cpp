// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi85> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi85> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi85__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvma_wr_rd_cntxt_c"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi85> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi85__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c, vlProcess, vlSymsp, "uvma_wr_rd_cntxt_c"s)
            : VL_NEW(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvma_wr_rd_cntxt_c"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_do_execute_op(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op> op) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_do_execute_op\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::__VnoInFunc_do_execute_op(vlProcess, vlSymsp, op);
    this->__VnoInFunc____05Fm_uvm_execute_field_op(vlProcess, vlSymsp, op);
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc____05Fm_uvm_execute_field_op(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op> ___05Flocal_op___05F) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc____05Fm_uvm_execute_field_op\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_get_rhs__5__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_get_rhs__6__Vfuncout;
    std::string __Vtask_get_name__7__Vfuncout;
    IData/*27:0*/ __Vtask_get_op_type__8__Vfuncout;
    __Vtask_get_op_type__8__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__9__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__10__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__11__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__12__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__13__Vfuncout;
    // Body
    IData/*27:0*/ local_op_type___05F;
    local_op_type___05F = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c> local_rhs___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> local_rsrc___05F;
    std::string local_rsrc_name___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> local_obj___05F;
    CData/*0:0*/ local_success___05F;
    local_success___05F = 0;
    IData/*31:0*/ local_size___05F;
    local_size___05F = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> ___05Flocal_printer___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer> ___05Flocal_comparer___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> ___05Flocal_recorder___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> ___05Flocal_packer___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_copier> ___05Flocal_copier___05F;
    {
        (void)VL_CAST_DYNAMIC(([&]() {
                    VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23)
                               ->__VnoInFunc_get_rhs(vlProcess, vlSymsp, __Vtask_get_rhs__5__Vfuncout);
                }(), __Vtask_get_rhs__5__Vfuncout), local_rhs___05F);
        if ((VL_CAST_DYNAMIC(([&]() {
                            VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23)
                              ->__VnoInFunc_get_rhs(vlProcess, vlSymsp, __Vtask_get_rhs__6__Vfuncout);
                        }(), __Vtask_get_rhs__6__Vfuncout), local_rsrc___05F) 
             && (VlNull{} != local_rsrc___05F))) {
            VL_NULL_CHECK(local_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23)->__VnoInFunc_get_name(vlSymsp, __Vtask_get_name__7__Vfuncout);
            local_rsrc_name___05F = __Vtask_get_name__7__Vfuncout;
        }
        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23)->__VnoInFunc_get_op_type(vlProcess, vlSymsp, __Vtask_get_op_type__8__Vfuncout);
        local_op_type___05F = __Vtask_get_op_type__8__Vfuncout;
        if ((0x00000010U == local_op_type___05F)) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__9__Vfuncout);
                                    }(), __Vtask_get_policy__9__Vfuncout), ___05Flocal_printer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvma_wr_rd_cntxt.svh:23: Assertion failed in %Nuvma_wr_rd_pkg.uvma_wr_rd_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23, "");
            }
        } else if ((4U == local_op_type___05F)) {
            if ((VlNull{} == local_rhs___05F)) {
                goto __Vlabel0;
            }
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__10__Vfuncout);
                                    }(), __Vtask_get_policy__10__Vfuncout), ___05Flocal_comparer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvma_wr_rd_cntxt.svh:23: Assertion failed in %Nuvma_wr_rd_pkg.uvma_wr_rd_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23, "");
            }
        } else if ((0x00000040U == local_op_type___05F)) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__11__Vfuncout);
                                    }(), __Vtask_get_policy__11__Vfuncout), ___05Flocal_recorder___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvma_wr_rd_cntxt.svh:23: Assertion failed in %Nuvma_wr_rd_pkg.uvma_wr_rd_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23, "");
            }
        } else if (((0x00000100U == local_op_type___05F) 
                    || (0x00000400U == local_op_type___05F))) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__12__Vfuncout);
                                    }(), __Vtask_get_policy__12__Vfuncout), ___05Flocal_packer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvma_wr_rd_cntxt.svh:23: Assertion failed in %Nuvma_wr_rd_pkg.uvma_wr_rd_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23, "");
            }
        } else if ((1U == local_op_type___05F)) {
            if ((VlNull{} == local_rhs___05F)) {
                goto __Vlabel0;
            }
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__13__Vfuncout);
                                    }(), __Vtask_get_policy__13__Vfuncout), ___05Flocal_copier___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvma_wr_rd_cntxt.svh:23: Assertion failed in %Nuvma_wr_rd_pkg.uvma_wr_rd_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_cntxt.svh", 23, "");
            }
        }
        __Vlabel0: ;
    }
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_object(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__16__Vfuncout;
    __Vfunc___VBasicRand__16__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__16__Vfuncout);
            }(), __Vfunc___VBasicRand__16__Vfuncout));
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__wr_vif = nullptr;
    __PVT__rd_vif = nullptr;
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                            uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += "wr_vif:" + VL_TO_STRING(__PVT__wr_vif);
    out += ", rd_vif:" + VL_TO_STRING(__PVT__rd_vif);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::to_string_middle();
    return (out);
}
