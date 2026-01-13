// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi82> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi82> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi82__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvme_fifo_random_vseq_c"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi82> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi82__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c, vlProcess, vlSymsp, "uvme_fifo_random_vseq"s)
            : VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvme_fifo_random_vseq_c"s;
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

VlCoroutine uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_body(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_body\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vfunc_self__5__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__28__Vfuncout;
    __Vfunc_uvm_report_enabled__28__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk3__DOT____VforkParent;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6> __VDynScope_body_0;
    __VDynScope_body_0 = VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6, vlSymsp);
    VL_NULL_CHECK(__VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 31)->__PVT__wr_sqr 
        = VL_NULL_CHECK(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__PVT__p_sequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 31)
        ->__PVT__write_sqr;
    VL_NULL_CHECK(__VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 32)->__PVT__rd_sqr 
        = VL_NULL_CHECK(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__PVT__p_sequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 32)
        ->__PVT__read_sqr;
    vlSymsp->TOP__std__03a__03aprocess__Vclpkg.__VnoInFunc_self(vlProcess, vlSymsp, __Vfunc_self__5__Vfuncout);
    unnamedblk3__DOT____VforkParent = __Vfunc_self__5__Vfuncout;
    this->__VnoInFunc_body____Vfork_1__0(std::make_shared<VlProcess>(vlProcess), vlSymsp, __VDynScope_body_0, unnamedblk3__DOT____VforkParent);
    this->__VnoInFunc_body____Vfork_1__1(std::make_shared<VlProcess>(vlProcess), vlSymsp, __VDynScope_body_0, unnamedblk3__DOT____VforkParent);
    co_await vlSymsp->TOP.__VdlySched.delay(0x00000000001e8480ULL, 
                                            vlProcess, 
                                            "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 
                                            63);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "RANDOM_VSEQ"s, __Vfunc_uvm_report_enabled__28__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__28__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "RANDOM_VSEQ"s, "uvme_fifo_random_vseq_c::body Finished."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh"s, 0x00000040U, ""s, 1U);
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_body____Vfork_1__1(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6> __VDynScope_body_0, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk3__DOT____VforkParent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_body____Vfork_1__1\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vtask___VforkTask_1__17____VforkParent;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6> __Vtask___VforkTask_1__17____VDynScope_body_0;
    IData/*31:0*/ __Vtask___VforkTask_1__17__unnamedblk1_2__DOT____Vrepeat1;
    __Vtask___VforkTask_1__17__unnamedblk1_2__DOT____Vrepeat1 = 0;
    IData/*31:0*/ __Vtask_status__18__Vfuncout;
    __Vtask_status__18__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__19__Vfuncout;
    __Vfunc_uvm_report_enabled__19__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c> __Vfunc_create__21__Vfuncout;
    IData/*31:0*/ __Vtask_randomize__22__Vfuncout;
    __Vtask_randomize__22__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__23__Vfuncout;
    __Vfunc_uvm_report_enabled__23__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__25__Vfuncout;
    __Vfunc_uvm_report_enabled__25__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    __Vtask___VforkTask_1__17____VDynScope_body_0 = __VDynScope_body_0;
    __Vtask___VforkTask_1__17____VforkParent = unnamedblk3__DOT____VforkParent;
    __Vtask___VforkTask_1__17__unnamedblk1_2__DOT____Vrepeat1 = 0;
    if ((1U == ([&]() {
                    VL_NULL_CHECK(__Vtask___VforkTask_1__17____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 37)
                ->__VnoInFunc_status(vlSymsp, __Vtask_status__18__Vfuncout);
                }(), __Vtask_status__18__Vfuncout))) {
        CData/*0:0*/ __VdynTrigger_h3fdd02b5__0;
        __VdynTrigger_h3fdd02b5__0 = 0;
        __VdynTrigger_h3fdd02b5__0 = 0U;
        while ((1U & (~ (IData)(__VdynTrigger_h3fdd02b5__0)))) {
            co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                         vlProcess, 
                                                         "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvme_fifo_pkg::uvme_fifo_random_vseq_c.__Vtask___VforkTask_1__17____VforkParent.(uvme_fifo_pkg::uvme_fifo_random_vseq_c.__Vtask_status__18__Vfuncout); , ); ))", 
                                                         "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 
                                                         37);
            this->__Vtrigprevexpr_h459257da__0 = (1U 
                                                  != 
                                                  ([&]() {
                        VL_NULL_CHECK(__Vtask___VforkTask_1__17____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 37)
                                                   ->__VnoInFunc_status(vlSymsp, __Vtask_status__18__Vfuncout);
                    }(), __Vtask_status__18__Vfuncout));
            __VdynTrigger_h3fdd02b5__0 = this->__Vtrigprevexpr_h459257da__0;
            vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_h3fdd02b5__0);
        }
        co_await vlSymsp->TOP.__VdynSched.resumption(
                                                     vlProcess, 
                                                     "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvme_fifo_pkg::uvme_fifo_random_vseq_c.__Vtask___VforkTask_1__17____VforkParent.(uvme_fifo_pkg::uvme_fifo_random_vseq_c.__Vtask_status__18__Vfuncout); , ); ))", 
                                                     "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 
                                                     37);
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "RANDOM_VSEQ"s, __Vfunc_uvm_report_enabled__19__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__19__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "RANDOM_VSEQ"s, "uvme_fifo_random_vseq_c::body Starting read sequence (100 items)."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh"s, 0x00000032U, ""s, 1U);
    }
    __Vtask___VforkTask_1__17__unnamedblk1_2__DOT____Vrepeat1 = 0x00000064U;
    while (VL_LTS_III(32, 0U, __Vtask___VforkTask_1__17__unnamedblk1_2__DOT____Vrepeat1)) {
        vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi93__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "rd_seq"s, VlNull{}, ""s, __Vfunc_create__21__Vfuncout);
        VL_NULL_CHECK(__Vtask___VforkTask_1__17____VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 52)->__PVT__rd_seq 
            = __Vfunc_create__21__Vfuncout;
        if ((1U & (~ (0U != ([&]() {
                                VL_NULL_CHECK(VL_NULL_CHECK(__Vtask___VforkTask_1__17____VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 53)
                                              ->__PVT__rd_seq, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 53)
                             ->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__22__Vfuncout);
                            }(), __Vtask_randomize__22__Vfuncout))))) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "RANDOM_VSEQ"s, __Vfunc_uvm_report_enabled__23__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__23__Vfuncout))) {
                this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "RANDOM_VSEQ"s, "uvme_fifo_random_vseq_c::body::rd_seq randomize failed"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh"s, 0x00000036U, ""s, 1U);
            }
        }
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "RANDOM_VSEQ"s, __Vfunc_uvm_report_enabled__25__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__25__Vfuncout))) {
            this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "RANDOM_VSEQ"s, "Generated read sequence item"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh"s, 0x00000038U, ""s, 1U);
        }
        co_await VL_NULL_CHECK(VL_NULL_CHECK(__Vtask___VforkTask_1__17____VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 57)
                               ->__PVT__rd_seq, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 57)->__VnoInFunc_start(vlProcess, vlSymsp, VL_NULL_CHECK(__Vtask___VforkTask_1__17____VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 57)
                                                                                ->__PVT__rd_sqr, VlNull{}, 0xffffffffU, 1U);
        __Vtask___VforkTask_1__17__unnamedblk1_2__DOT____Vrepeat1 
            = (__Vtask___VforkTask_1__17__unnamedblk1_2__DOT____Vrepeat1 
               - (IData)(1U));
    }
    vlProcess->state(VlProcess::FINISHED);
    co_return;}

VlCoroutine uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_body____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6> __VDynScope_body_0, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk3__DOT____VforkParent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_body____Vfork_1__0\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vtask___VforkTask_0__6____VforkParent;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6> __Vtask___VforkTask_0__6____VDynScope_body_0;
    IData/*31:0*/ __Vtask___VforkTask_0__6__unnamedblk1_1__DOT____Vrepeat0;
    __Vtask___VforkTask_0__6__unnamedblk1_1__DOT____Vrepeat0 = 0;
    IData/*31:0*/ __Vtask_status__7__Vfuncout;
    __Vtask_status__7__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__8__Vfuncout;
    __Vfunc_uvm_report_enabled__8__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_random_seq_c> __Vfunc_create__10__Vfuncout;
    IData/*31:0*/ __Vtask_randomize__11__Vfuncout;
    __Vtask_randomize__11__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__12__Vfuncout;
    __Vfunc_uvm_report_enabled__12__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__14__Vfuncout;
    __Vfunc_uvm_report_enabled__14__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    __Vtask___VforkTask_0__6____VDynScope_body_0 = __VDynScope_body_0;
    __Vtask___VforkTask_0__6____VforkParent = unnamedblk3__DOT____VforkParent;
    __Vtask___VforkTask_0__6__unnamedblk1_1__DOT____Vrepeat0 = 0;
    if ((1U == ([&]() {
                    VL_NULL_CHECK(__Vtask___VforkTask_0__6____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 37)
                ->__VnoInFunc_status(vlSymsp, __Vtask_status__7__Vfuncout);
                }(), __Vtask_status__7__Vfuncout))) {
        CData/*0:0*/ __VdynTrigger_he9fd7a6a__0;
        __VdynTrigger_he9fd7a6a__0 = 0;
        __VdynTrigger_he9fd7a6a__0 = 0U;
        while ((1U & (~ (IData)(__VdynTrigger_he9fd7a6a__0)))) {
            co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                         vlProcess, 
                                                         "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvme_fifo_pkg::uvme_fifo_random_vseq_c.__Vtask___VforkTask_0__6____VforkParent.(uvme_fifo_pkg::uvme_fifo_random_vseq_c.__Vtask_status__7__Vfuncout); , ); ))", 
                                                         "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 
                                                         37);
            this->__Vtrigprevexpr_hdbf1cfa5__0 = (1U 
                                                  != 
                                                  ([&]() {
                        VL_NULL_CHECK(__Vtask___VforkTask_0__6____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 37)
                                                   ->__VnoInFunc_status(vlSymsp, __Vtask_status__7__Vfuncout);
                    }(), __Vtask_status__7__Vfuncout));
            __VdynTrigger_he9fd7a6a__0 = this->__Vtrigprevexpr_hdbf1cfa5__0;
            vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_he9fd7a6a__0);
        }
        co_await vlSymsp->TOP.__VdynSched.resumption(
                                                     vlProcess, 
                                                     "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvme_fifo_pkg::uvme_fifo_random_vseq_c.__Vtask___VforkTask_0__6____VforkParent.(uvme_fifo_pkg::uvme_fifo_random_vseq_c.__Vtask_status__7__Vfuncout); , ); ))", 
                                                     "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 
                                                     37);
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "RANDOM_VSEQ"s, __Vfunc_uvm_report_enabled__8__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__8__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "RANDOM_VSEQ"s, "uvme_fifo_random_vseq_c::body Starting write sequence (100 items)."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh"s, 0x00000027U, ""s, 1U);
    }
    __Vtask___VforkTask_0__6__unnamedblk1_1__DOT____Vrepeat0 = 0x00000064U;
    while (VL_LTS_III(32, 0U, __Vtask___VforkTask_0__6__unnamedblk1_1__DOT____Vrepeat0)) {
        vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi92__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "wr_seq"s, VlNull{}, ""s, __Vfunc_create__10__Vfuncout);
        VL_NULL_CHECK(__Vtask___VforkTask_0__6____VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 41)->__PVT__wr_seq 
            = __Vfunc_create__10__Vfuncout;
        if ((1U & (~ (0U != ([&]() {
                                VL_NULL_CHECK(VL_NULL_CHECK(__Vtask___VforkTask_0__6____VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 42)
                                              ->__PVT__wr_seq, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 42)
                             ->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__11__Vfuncout);
                            }(), __Vtask_randomize__11__Vfuncout))))) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "RANDOM_VSEQ"s, __Vfunc_uvm_report_enabled__12__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__12__Vfuncout))) {
                this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "RANDOM_VSEQ"s, "uvme_fifo_random_vseq_c::body::wr_seq randomize failed"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh"s, 0x0000002bU, ""s, 1U);
            }
        }
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "RANDOM_VSEQ"s, __Vfunc_uvm_report_enabled__14__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__14__Vfuncout))) {
            this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "RANDOM_VSEQ"s, "Generated write sequence item"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh"s, 0x0000002dU, ""s, 1U);
        }
        co_await VL_NULL_CHECK(VL_NULL_CHECK(__Vtask___VforkTask_0__6____VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 46)
                               ->__PVT__wr_seq, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 46)->__VnoInFunc_start(vlProcess, vlSymsp, VL_NULL_CHECK(__Vtask___VforkTask_0__6____VDynScope_body_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_random_vseq.svh", 46)
                                                                                ->__PVT__wr_sqr, VlNull{}, 0xffffffffU, 1U);
        __Vtask___VforkTask_0__6__unnamedblk1_1__DOT____Vrepeat0 
            = (__Vtask___VforkTask_0__6__unnamedblk1_1__DOT____Vrepeat0 
               - (IData)(1U));
    }
    vlProcess->state(VlProcess::FINISHED);
    co_return;}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__31__Vfuncout;
    __Vfunc___VBasicRand__31__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__31__Vfuncout);
            }(), __Vfunc___VBasicRand__31__Vfuncout));
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __Vtrigprevexpr_hdbf1cfa5__0 = 0;
    __Vtrigprevexpr_h459257da__0 = 0;
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::to_string_middle();
    return (out);
}
