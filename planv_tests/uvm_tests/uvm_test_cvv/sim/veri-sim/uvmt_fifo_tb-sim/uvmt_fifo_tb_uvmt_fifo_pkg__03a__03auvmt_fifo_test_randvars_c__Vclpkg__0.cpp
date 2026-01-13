// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi67> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi67> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi67__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvmt_fifo_test_randvars_c"s;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi67> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi67__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c, vlProcess, vlSymsp, "uvmt_fifo_test_randvars"s)
            : VL_NEW(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvmt_fifo_test_randvars_c"s;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_do_execute_op(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op> op) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_do_execute_op\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::__VnoInFunc_do_execute_op(vlProcess, vlSymsp, op);
    this->__VnoInFunc____05Fm_uvm_execute_field_op(vlProcess, vlSymsp, op);
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc____05Fm_uvm_execute_field_op(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op> ___05Flocal_op___05F) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc____05Fm_uvm_execute_field_op\n"); );
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
    IData/*31:0*/ __Vtask_get_threshold__14__Vfuncout;
    __Vtask_get_threshold__14__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__15__Vfuncout;
    __Vtask_get_result__15__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__16__Vfuncout;
    __Vtask_get_threshold__16__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_field_int__17__Vfuncout;
    __Vtask_compare_field_int__17__Vfuncout = 0;
    CData/*0:0*/ __Vtask_is_open__20__Vfuncout;
    __Vtask_is_open__20__Vfuncout = 0;
    CData/*0:0*/ __Vtask_use_record_attribute__21__Vfuncout;
    __Vtask_use_record_attribute__21__Vfuncout = 0;
    QData/*63:0*/ __Vtask_read__25__Vfuncout;
    __Vtask_read__25__Vfuncout = 0;
    VlWide<128>/*4095:0*/ __Vtask_read__26__Vfuncout;
    VL_ZERO_W(4096, __Vtask_read__26__Vfuncout);
    IData/*31:0*/ __Vtask_read__27__Vfuncout;
    __Vtask_read__27__Vfuncout = 0;
    IData/*31:0*/ __Vtask_read__28__Vfuncout;
    __Vtask_read__28__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__29__Vfuncout;
    __Vtask_get_threshold__29__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__30__Vfuncout;
    __Vtask_get_result__30__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__31__Vfuncout;
    __Vtask_get_threshold__31__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_field_int__32__Vfuncout;
    __Vtask_compare_field_int__32__Vfuncout = 0;
    CData/*0:0*/ __Vtask_is_open__35__Vfuncout;
    __Vtask_is_open__35__Vfuncout = 0;
    CData/*0:0*/ __Vtask_use_record_attribute__36__Vfuncout;
    __Vtask_use_record_attribute__36__Vfuncout = 0;
    QData/*63:0*/ __Vtask_read__40__Vfuncout;
    __Vtask_read__40__Vfuncout = 0;
    VlWide<128>/*4095:0*/ __Vtask_read__41__Vfuncout;
    VL_ZERO_W(4096, __Vtask_read__41__Vfuncout);
    IData/*31:0*/ __Vtask_read__42__Vfuncout;
    __Vtask_read__42__Vfuncout = 0;
    IData/*31:0*/ __Vtask_read__43__Vfuncout;
    __Vtask_read__43__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__44__Vfuncout;
    __Vtask_get_threshold__44__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__45__Vfuncout;
    __Vtask_get_result__45__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__46__Vfuncout;
    __Vtask_get_threshold__46__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_field_int__47__Vfuncout;
    __Vtask_compare_field_int__47__Vfuncout = 0;
    CData/*0:0*/ __Vtask_is_open__50__Vfuncout;
    __Vtask_is_open__50__Vfuncout = 0;
    CData/*0:0*/ __Vtask_use_record_attribute__51__Vfuncout;
    __Vtask_use_record_attribute__51__Vfuncout = 0;
    QData/*63:0*/ __Vtask_read__55__Vfuncout;
    __Vtask_read__55__Vfuncout = 0;
    VlWide<128>/*4095:0*/ __Vtask_read__56__Vfuncout;
    VL_ZERO_W(4096, __Vtask_read__56__Vfuncout);
    IData/*31:0*/ __Vtask_read__57__Vfuncout;
    __Vtask_read__57__Vfuncout = 0;
    IData/*31:0*/ __Vtask_read__58__Vfuncout;
    __Vtask_read__58__Vfuncout = 0;
    // Body
    VlQueue<CData/*0:0*/> unnamedblk1__DOT_____05Farray;
    unnamedblk1__DOT_____05Farray.atDefault() = 0;
    VlQueue<CData/*0:0*/> unnamedblk2__DOT_____05Farray;
    unnamedblk2__DOT_____05Farray.atDefault() = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz15> unnamedblk3__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz14> unnamedblk4__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_> unnamedblk5__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz16> unnamedblk6__DOT_____05Ftmp_rsrc___05F;
    VlQueue<CData/*0:0*/> unnamedblk7__DOT_____05Farray;
    unnamedblk7__DOT_____05Farray.atDefault() = 0;
    VlQueue<CData/*0:0*/> unnamedblk8__DOT_____05Farray;
    unnamedblk8__DOT_____05Farray.atDefault() = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz15> unnamedblk9__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz14> unnamedblk10__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_> unnamedblk11__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz16> unnamedblk12__DOT_____05Ftmp_rsrc___05F;
    VlQueue<CData/*0:0*/> unnamedblk13__DOT_____05Farray;
    unnamedblk13__DOT_____05Farray.atDefault() = 0;
    VlQueue<CData/*0:0*/> unnamedblk14__DOT_____05Farray;
    unnamedblk14__DOT_____05Farray.atDefault() = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz15> unnamedblk15__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz14> unnamedblk16__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_> unnamedblk17__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz16> unnamedblk18__DOT_____05Ftmp_rsrc___05F;
    IData/*27:0*/ local_op_type___05F;
    local_op_type___05F = 0;
    VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c> local_rhs___05F;
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
                    VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19)
                               ->__VnoInFunc_get_rhs(vlProcess, vlSymsp, __Vtask_get_rhs__5__Vfuncout);
                }(), __Vtask_get_rhs__5__Vfuncout), local_rhs___05F);
        if ((VL_CAST_DYNAMIC(([&]() {
                            VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19)
                              ->__VnoInFunc_get_rhs(vlProcess, vlSymsp, __Vtask_get_rhs__6__Vfuncout);
                        }(), __Vtask_get_rhs__6__Vfuncout), local_rsrc___05F) 
             && (VlNull{} != local_rsrc___05F))) {
            VL_NULL_CHECK(local_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19)->__VnoInFunc_get_name(vlSymsp, __Vtask_get_name__7__Vfuncout);
            local_rsrc_name___05F = __Vtask_get_name__7__Vfuncout;
        }
        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19)->__VnoInFunc_get_op_type(vlProcess, vlSymsp, __Vtask_get_op_type__8__Vfuncout);
        local_op_type___05F = __Vtask_get_op_type__8__Vfuncout;
        if ((0x00000010U == local_op_type___05F)) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__9__Vfuncout);
                                    }(), __Vtask_get_policy__9__Vfuncout), ___05Flocal_printer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvmt_fifo_test_randvars.svh:19: Assertion failed in %Nuvmt_fifo_pkg.uvmt_fifo_test_randvars_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19, "");
            }
        } else if ((4U == local_op_type___05F)) {
            if ((VlNull{} == local_rhs___05F)) {
                goto __Vlabel0;
            }
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__10__Vfuncout);
                                    }(), __Vtask_get_policy__10__Vfuncout), ___05Flocal_comparer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvmt_fifo_test_randvars.svh:19: Assertion failed in %Nuvmt_fifo_pkg.uvmt_fifo_test_randvars_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19, "");
            }
        } else if ((0x00000040U == local_op_type___05F)) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__11__Vfuncout);
                                    }(), __Vtask_get_policy__11__Vfuncout), ___05Flocal_recorder___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvmt_fifo_test_randvars.svh:19: Assertion failed in %Nuvmt_fifo_pkg.uvmt_fifo_test_randvars_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19, "");
            }
        } else if (((0x00000100U == local_op_type___05F) 
                    || (0x00000400U == local_op_type___05F))) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__12__Vfuncout);
                                    }(), __Vtask_get_policy__12__Vfuncout), ___05Flocal_packer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvmt_fifo_test_randvars.svh:19: Assertion failed in %Nuvmt_fifo_pkg.uvmt_fifo_test_randvars_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19, "");
            }
        } else if ((1U == local_op_type___05F)) {
            if ((VlNull{} == local_rhs___05F)) {
                goto __Vlabel0;
            }
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__13__Vfuncout);
                                    }(), __Vtask_get_policy__13__Vfuncout), ___05Flocal_copier___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvmt_fifo_test_randvars.svh:19: Assertion failed in %Nuvmt_fifo_pkg.uvmt_fifo_test_randvars_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 19, "");
            }
        } else if ((0x00000800U == local_op_type___05F)) {
            if ((VlNull{} == local_rsrc___05F)) {
                goto __Vlabel0;
            }
        } else {
            goto __Vlabel0;
        }
        if ((1U == local_op_type___05F)) {
            this->__PVT__random_int = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                ->__PVT__random_int;
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__14__Vfuncout);
                                    }(), __Vtask_get_threshold__14__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__15__Vfuncout);
                            }(), __Vtask_get_result__15__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__16__Vfuncout);
                            }(), __Vtask_get_threshold__16__Vfuncout)))) {
                if ((this->__PVT__random_int != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                     ->__PVT__random_int)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)->__VnoInFunc_compare_field_int(vlProcess, vlSymsp, "random_int"s, (QData)((IData)(this->__PVT__random_int)), (QData)((IData)(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                                                                                ->__PVT__random_int)), 0x00000020U, 0U, __Vtask_compare_field_int__17__Vfuncout);
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_UNPACK_RI_I(1, 32, unnamedblk1__DOT_____05Farray, VL_STREAML_FAST_III(32, this->__PVT__random_int, 0));
            unnamedblk1__DOT_____05Farray.renew_copy(0x00000020U, unnamedblk1__DOT_____05Farray);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)->__VnoInFunc_pack_bits(vlProcess, vlSymsp, unnamedblk1__DOT_____05Farray, 0x00000020U);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk2__DOT_____05Farray.renew(0x00000020U);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)->__VnoInFunc_unpack_bits(vlProcess, vlSymsp, unnamedblk2__DOT_____05Farray, 0x00000020U);
            unnamedblk2__DOT_____05Farray.renew_copy(0x00000020U, unnamedblk2__DOT_____05Farray);
            this->__PVT__random_int = VL_STREAML_FAST_III(32, VL_PACK_I_RI
                                                          (32, 1, unnamedblk2__DOT_____05Farray), 0);
        } else if ((0x00000040U == local_op_type___05F)) {
            if (((VlNull{} != ___05Flocal_recorder___05F) 
                 && ([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                     ->__VnoInFunc_is_open(vlSymsp, __Vtask_is_open__20__Vfuncout);
                        }(), (IData)(__Vtask_is_open__20__Vfuncout)))) {
                if (([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                     ->__VnoInFunc_use_record_attribute(vlSymsp, __Vtask_use_record_attribute__21__Vfuncout);
                        }(), (IData)(__Vtask_use_record_attribute__21__Vfuncout))) {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)->__VnoInFunc_record_generic(vlProcess, vlSymsp, "random_int"s, VL_SFORMATF_N_NX("%0#",0,
                                                                                32,
                                                                                this->__PVT__random_int) , ""s);
                } else {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)->__VnoInFunc_record_field_int(vlProcess, vlSymsp, "random_int"s, (QData)((IData)(this->__PVT__random_int)), 0x00000020U, 0U);
                }
            }
        } else if ((0x00000010U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)->__VnoInFunc_print_field_int(vlProcess, vlSymsp, "random_int"s, (QData)((IData)(this->__PVT__random_int)), 0x00000020U, 0U, 0x2eU, "integral"s);
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("random_int"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk3__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    this->__PVT__random_int = (IData)(
                                                      ([&]() {
                                VL_NULL_CHECK(unnamedblk3__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                                                       ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                          VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__25__Vfuncout);
                            }(), __Vtask_read__25__Vfuncout));
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk4__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__random_int = VL_SEL_IWII(4096, 
                                                              ([&]() {
                                    VL_NULL_CHECK(unnamedblk4__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)
                                                               ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__26__Vfuncout);
                                }(), __Vtask_read__26__Vfuncout), 0U, 32);
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk5__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        VL_NULL_CHECK(unnamedblk5__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__27__Vfuncout);
                        this->__PVT__random_int = __Vtask_read__27__Vfuncout;
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk6__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        VL_NULL_CHECK(unnamedblk6__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 20)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__28__Vfuncout);
                        this->__PVT__random_int = __Vtask_read__28__Vfuncout;
                    }
                }
            }
        }
        if ((1U == local_op_type___05F)) {
            this->__PVT__random_logic32 = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                ->__PVT__random_logic32;
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__29__Vfuncout);
                                    }(), __Vtask_get_threshold__29__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__30__Vfuncout);
                            }(), __Vtask_get_result__30__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__31__Vfuncout);
                            }(), __Vtask_get_threshold__31__Vfuncout)))) {
                if ((this->__PVT__random_logic32 != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                     ->__PVT__random_logic32)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)->__VnoInFunc_compare_field_int(vlProcess, vlSymsp, "random_logic32"s, (QData)((IData)(this->__PVT__random_logic32)), (QData)((IData)(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                                                                                ->__PVT__random_logic32)), 0x00000020U, 0U, __Vtask_compare_field_int__32__Vfuncout);
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_UNPACK_RI_I(1, 32, unnamedblk7__DOT_____05Farray, VL_STREAML_FAST_III(32, this->__PVT__random_logic32, 0));
            unnamedblk7__DOT_____05Farray.renew_copy(0x00000020U, unnamedblk7__DOT_____05Farray);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)->__VnoInFunc_pack_bits(vlProcess, vlSymsp, unnamedblk7__DOT_____05Farray, 0x00000020U);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk8__DOT_____05Farray.renew(0x00000020U);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)->__VnoInFunc_unpack_bits(vlProcess, vlSymsp, unnamedblk8__DOT_____05Farray, 0x00000020U);
            unnamedblk8__DOT_____05Farray.renew_copy(0x00000020U, unnamedblk8__DOT_____05Farray);
            this->__PVT__random_logic32 = VL_STREAML_FAST_III(32, VL_PACK_I_RI
                                                              (32, 1, unnamedblk8__DOT_____05Farray), 0);
        } else if ((0x00000040U == local_op_type___05F)) {
            if (((VlNull{} != ___05Flocal_recorder___05F) 
                 && ([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                     ->__VnoInFunc_is_open(vlSymsp, __Vtask_is_open__35__Vfuncout);
                        }(), (IData)(__Vtask_is_open__35__Vfuncout)))) {
                if (([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                     ->__VnoInFunc_use_record_attribute(vlSymsp, __Vtask_use_record_attribute__36__Vfuncout);
                        }(), (IData)(__Vtask_use_record_attribute__36__Vfuncout))) {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)->__VnoInFunc_record_generic(vlProcess, vlSymsp, "random_logic32"s, VL_SFORMATF_N_NX("%0#",0,
                                                                                32,
                                                                                this->__PVT__random_logic32) , ""s);
                } else {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)->__VnoInFunc_record_field_int(vlProcess, vlSymsp, "random_logic32"s, (QData)((IData)(this->__PVT__random_logic32)), 0x00000020U, 0U);
                }
            }
        } else if ((0x00000010U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)->__VnoInFunc_print_field_int(vlProcess, vlSymsp, "random_logic32"s, (QData)((IData)(this->__PVT__random_logic32)), 0x00000020U, 0U, 0x2eU, "integral"s);
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("random_logic32"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk9__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    this->__PVT__random_logic32 = (IData)(
                                                          ([&]() {
                                VL_NULL_CHECK(unnamedblk9__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                                                           ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                              VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__40__Vfuncout);
                            }(), __Vtask_read__40__Vfuncout));
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk10__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__random_logic32 
                            = VL_SEL_IWII(4096, ([&]() {
                                    VL_NULL_CHECK(unnamedblk10__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)
                                                 ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                    VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__41__Vfuncout);
                                }(), __Vtask_read__41__Vfuncout), 0U, 32);
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk11__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        VL_NULL_CHECK(unnamedblk11__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__42__Vfuncout);
                        this->__PVT__random_logic32 
                            = __Vtask_read__42__Vfuncout;
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk12__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        VL_NULL_CHECK(unnamedblk12__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 21)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__43__Vfuncout);
                        this->__PVT__random_logic32 
                            = __Vtask_read__43__Vfuncout;
                    }
                }
            }
        }
        if ((1U == local_op_type___05F)) {
            this->__PVT__random_logic_bit = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                ->__PVT__random_logic_bit;
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__44__Vfuncout);
                                    }(), __Vtask_get_threshold__44__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__45__Vfuncout);
                            }(), __Vtask_get_result__45__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__46__Vfuncout);
                            }(), __Vtask_get_threshold__46__Vfuncout)))) {
                if (((IData)(this->__PVT__random_logic_bit) 
                     != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                     ->__PVT__random_logic_bit)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)->__VnoInFunc_compare_field_int(vlProcess, vlSymsp, "random_logic_bit"s, (QData)((IData)(this->__PVT__random_logic_bit)), (QData)((IData)(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                                                                                ->__PVT__random_logic_bit)), 1U, 0U, __Vtask_compare_field_int__47__Vfuncout);
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_UNPACK_RI_I(1, 1, unnamedblk13__DOT_____05Farray, VL_STREAML_FAST_III(1, (IData)(this->__PVT__random_logic_bit), 0));
            unnamedblk13__DOT_____05Farray.renew_copy(1U, unnamedblk13__DOT_____05Farray);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)->__VnoInFunc_pack_bits(vlProcess, vlSymsp, unnamedblk13__DOT_____05Farray, 1U);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk14__DOT_____05Farray.renew(1U);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)->__VnoInFunc_unpack_bits(vlProcess, vlSymsp, unnamedblk14__DOT_____05Farray, 1U);
            unnamedblk14__DOT_____05Farray.renew_copy(1U, unnamedblk14__DOT_____05Farray);
            this->__PVT__random_logic_bit = VL_STREAML_FAST_III(1, VL_PACK_I_RI
                                                                (1, 1, unnamedblk14__DOT_____05Farray), 0);
        } else if ((0x00000040U == local_op_type___05F)) {
            if (((VlNull{} != ___05Flocal_recorder___05F) 
                 && ([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                     ->__VnoInFunc_is_open(vlSymsp, __Vtask_is_open__50__Vfuncout);
                        }(), (IData)(__Vtask_is_open__50__Vfuncout)))) {
                if (([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                     ->__VnoInFunc_use_record_attribute(vlSymsp, __Vtask_use_record_attribute__51__Vfuncout);
                        }(), (IData)(__Vtask_use_record_attribute__51__Vfuncout))) {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)->__VnoInFunc_record_generic(vlProcess, vlSymsp, "random_logic_bit"s, VL_SFORMATF_N_NX("%0#",0,
                                                                                1,
                                                                                this->__PVT__random_logic_bit) , ""s);
                } else {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)->__VnoInFunc_record_field_int(vlProcess, vlSymsp, "random_logic_bit"s, (QData)((IData)(this->__PVT__random_logic_bit)), 1U, 0U);
                }
            }
        } else if ((0x00000010U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)->__VnoInFunc_print_field_int(vlProcess, vlSymsp, "random_logic_bit"s, (QData)((IData)(this->__PVT__random_logic_bit)), 1U, 0U, 0x2eU, "integral"s);
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("random_logic_bit"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk15__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    this->__PVT__random_logic_bit = 
                        (1U & (IData)(([&]() {
                                    VL_NULL_CHECK(unnamedblk15__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                                       ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                          VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__55__Vfuncout);
                                }(), __Vtask_read__55__Vfuncout)));
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk16__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__random_logic_bit 
                            = (1U & VL_BITSEL_IWII(4096, 
                                                   ([&]() {
                                        VL_NULL_CHECK(unnamedblk16__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                                                    ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                       VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__56__Vfuncout);
                                    }(), __Vtask_read__56__Vfuncout), 0U));
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk17__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__random_logic_bit 
                            = (1U & ([&]() {
                                    VL_NULL_CHECK(unnamedblk17__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                                     ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                        VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__57__Vfuncout);
                                }(), __Vtask_read__57__Vfuncout));
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk18__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__random_logic_bit 
                            = (1U & ([&]() {
                                    VL_NULL_CHECK(unnamedblk18__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_test_randvars.svh", 22)
                                     ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                        VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>{this}, __Vtask_read__58__Vfuncout);
                                }(), __Vtask_read__58__Vfuncout));
                    }
                }
            }
        }
        __Vlabel0: ;
    }
}

uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_object(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__61__Vfuncout;
    __Vfunc___VBasicRand__61__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__61__Vfuncout);
            }(), __Vfunc___VBasicRand__61__Vfuncout));
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
    this->__PVT__random_int = VL_RANDOM_RNG_I(__Vm_rng);
    this->__PVT__random_logic32 = VL_RANDOM_RNG_I(__Vm_rng);
    this->__PVT__random_logic_bit = (1U & VL_RANDOM_RNG_I(__Vm_rng));
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__random_int = 0;
    __PVT__random_logic32 = VL_SCOPED_RAND_RESET_I(32, 7376212610992925365ULL, 4927471376716534672ull);
    __PVT__random_logic_bit = VL_SCOPED_RAND_RESET_I(1, 7376212610992925365ULL, 9041832559856681356ull);
}

uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::~uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += "random_int:" + VL_TO_STRING(__PVT__random_int);
    out += ", random_logic32:" + VL_TO_STRING(__PVT__random_logic32);
    out += ", random_logic_bit:" + VL_TO_STRING(__PVT__random_logic_bit);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::to_string_middle();
    return (out);
}
