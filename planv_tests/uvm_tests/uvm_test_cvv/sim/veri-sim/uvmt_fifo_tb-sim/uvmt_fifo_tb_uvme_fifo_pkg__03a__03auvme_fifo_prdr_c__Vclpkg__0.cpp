// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi76> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi76> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi76__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvme_fifo_prdr_c"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi76> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi76__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvme_fifo_prdr_c"s;
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_component(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    this->__PVT__fifo_depth = 0x00000010U;
    ;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_build_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__3__Vfuncout;
    __Vfunc_uvm_report_enabled__3__Vfuncout = 0;
    CData/*0:0*/ __Vtask_get__5__Vfuncout;
    __Vtask_get__5__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c> __Vtask_get__5__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__6__Vfuncout;
    __Vfunc_uvm_report_enabled__6__Vfuncout = 0;
    CData/*0:0*/ __Vtask_get__8__Vfuncout;
    __Vtask_get__8__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c> __Vtask_get__8__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__9__Vfuncout;
    __Vfunc_uvm_report_enabled__9__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__15__Vfuncout;
    __Vfunc_uvm_report_enabled__15__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_build_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "PRDR"s, __Vfunc_uvm_report_enabled__3__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__3__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "PRDR"s, "Entered build_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x00000045U, ""s, 1U);
    }
    __Vtask_get__5__value = this->__PVT__cfg;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz146__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c>{this}, ""s, "cfg"s, __Vtask_get__5__value, __Vtask_get__5__Vfuncout);
    this->__PVT__cfg = __Vtask_get__5__value;
    if ((VlNull{} == this->__PVT__cfg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "CFG"s, __Vfunc_uvm_report_enabled__6__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__6__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "CFG"s, "cfg is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x00000049U, ""s, 1U);
        }
    }
    __Vtask_get__8__value = this->__PVT__cntxt;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz147__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c>{this}, ""s, "cntxt"s, __Vtask_get__8__value, __Vtask_get__8__Vfuncout);
    this->__PVT__cntxt = __Vtask_get__8__value;
    if ((VlNull{} == this->__PVT__cntxt)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "CNTXT"s, __Vfunc_uvm_report_enabled__9__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__9__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "CNTXT"s, "cntxt is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x0000004eU, ""s, 1U);
        }
    }
    this->__PVT__wr_input_imp = VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74, vlProcess, vlSymsp, "wr_input_imp"s, 
                                       VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c>{this});
    this->__PVT__rd_input_imp = VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_input__pi75, vlProcess, vlSymsp, "rd_input_imp"s, 
                                       VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c>{this});
    this->__PVT__wr_output_port = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz154, vlProcess, vlSymsp, "wr_output_port"s, 
                                         VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c>{this});
    this->__PVT__rd_output_port = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz155, vlProcess, vlSymsp, "rd_output_port"s, 
                                         VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c>{this});
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "PRDR"s, __Vfunc_uvm_report_enabled__15__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__15__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "PRDR"s, "Exiting build_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x00000058U, ""s, 1U);
    }
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_connect_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_connect_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__18__Vfuncout;
    __Vfunc_uvm_report_enabled__18__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__20__Vfuncout;
    __Vfunc_uvm_report_enabled__20__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_connect_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "PRDR"s, __Vfunc_uvm_report_enabled__18__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__18__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "PRDR"s, "Entered connect_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x00000061U, ""s, 1U);
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "PRDR"s, __Vfunc_uvm_report_enabled__20__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__20__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "PRDR"s, "Exiting connect_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x00000065U, ""s, 1U);
    }
}

VlCoroutine uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_run_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_run_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__23__Vfuncout;
    __Vfunc_uvm_report_enabled__23__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vfunc_self__25__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__32__Vfuncout;
    __Vfunc_uvm_report_enabled__32__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk1__DOT____VforkParent;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> wr_tr;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> rd_tr;
    co_await uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_run_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "PRDR"s, __Vfunc_uvm_report_enabled__23__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__23__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "PRDR"s, "Entered run_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x00000071U, ""s, 1U);
    }
    vlSymsp->TOP__std__03a__03aprocess__Vclpkg.__VnoInFunc_self(vlProcess, vlSymsp, __Vfunc_self__25__Vfuncout);
    unnamedblk1__DOT____VforkParent = __Vfunc_self__25__Vfuncout;
    this->__VnoInFunc_run_phase____Vfork_1__0(std::make_shared<VlProcess>(vlProcess), vlSymsp, wr_tr, unnamedblk1__DOT____VforkParent);
    this->__VnoInFunc_run_phase____Vfork_1__1(std::make_shared<VlProcess>(vlProcess), vlSymsp, rd_tr, unnamedblk1__DOT____VforkParent);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "PRDR"s, __Vfunc_uvm_report_enabled__32__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__32__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "PRDR"s, "Exiting run_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x00000078U, ""s, 1U);
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_run_phase____Vfork_1__1(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> rd_tr, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk1__DOT____VforkParent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_run_phase____Vfork_1__1\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vtask___VforkTask_1__29____VforkParent;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> __Vtask___VforkTask_1__29__rd_tr;
    IData/*31:0*/ __Vtask_status__30__Vfuncout;
    __Vtask_status__30__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    __Vtask___VforkTask_1__29__rd_tr = rd_tr;
    __Vtask___VforkTask_1__29____VforkParent = unnamedblk1__DOT____VforkParent;
    if ((1U == ([&]() {
                    VL_NULL_CHECK(__Vtask___VforkTask_1__29____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 115)
                ->__VnoInFunc_status(vlSymsp, __Vtask_status__30__Vfuncout);
                }(), __Vtask_status__30__Vfuncout))) {
        CData/*0:0*/ __VdynTrigger_hcdab7c5d__0;
        __VdynTrigger_hcdab7c5d__0 = 0;
        __VdynTrigger_hcdab7c5d__0 = 0U;
        while ((1U & (~ (IData)(__VdynTrigger_hcdab7c5d__0)))) {
            co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                         vlProcess, 
                                                         "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvme_fifo_pkg::uvme_fifo_prdr_c.__Vtask___VforkTask_1__29____VforkParent.(uvme_fifo_pkg::uvme_fifo_prdr_c.__Vtask_status__30__Vfuncout); , ); ))", 
                                                         "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 
                                                         115);
            this->__Vtrigprevexpr_hb7c3d9d2__0 = (1U 
                                                  != 
                                                  ([&]() {
                        VL_NULL_CHECK(__Vtask___VforkTask_1__29____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 115)
                                                   ->__VnoInFunc_status(vlSymsp, __Vtask_status__30__Vfuncout);
                    }(), __Vtask_status__30__Vfuncout));
            __VdynTrigger_hcdab7c5d__0 = this->__Vtrigprevexpr_hb7c3d9d2__0;
            vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_hcdab7c5d__0);
        }
        co_await vlSymsp->TOP.__VdynSched.resumption(
                                                     vlProcess, 
                                                     "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvme_fifo_pkg::uvme_fifo_prdr_c.__Vtask___VforkTask_1__29____VforkParent.(uvme_fifo_pkg::uvme_fifo_prdr_c.__Vtask_status__30__Vfuncout); , ); ))", 
                                                     "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 
                                                     115);
    }
    co_await this->__VnoInFunc_process_read(vlProcess, vlSymsp, __Vtask___VforkTask_1__29__rd_tr);
    vlProcess->state(VlProcess::FINISHED);
    co_return;}

VlCoroutine uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_run_phase____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> wr_tr, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk1__DOT____VforkParent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_run_phase____Vfork_1__0\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vtask___VforkTask_0__26____VforkParent;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> __Vtask___VforkTask_0__26__wr_tr;
    IData/*31:0*/ __Vtask_status__27__Vfuncout;
    __Vtask_status__27__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    __Vtask___VforkTask_0__26__wr_tr = wr_tr;
    __Vtask___VforkTask_0__26____VforkParent = unnamedblk1__DOT____VforkParent;
    if ((1U == ([&]() {
                    VL_NULL_CHECK(__Vtask___VforkTask_0__26____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 115)
                ->__VnoInFunc_status(vlSymsp, __Vtask_status__27__Vfuncout);
                }(), __Vtask_status__27__Vfuncout))) {
        CData/*0:0*/ __VdynTrigger_hcbe693c9__0;
        __VdynTrigger_hcbe693c9__0 = 0;
        __VdynTrigger_hcbe693c9__0 = 0U;
        while ((1U & (~ (IData)(__VdynTrigger_hcbe693c9__0)))) {
            co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                         vlProcess, 
                                                         "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvme_fifo_pkg::uvme_fifo_prdr_c.__Vtask___VforkTask_0__26____VforkParent.(uvme_fifo_pkg::uvme_fifo_prdr_c.__Vtask_status__27__Vfuncout); , ); ))", 
                                                         "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 
                                                         115);
            this->__Vtrigprevexpr_hb998f206__0 = (1U 
                                                  != 
                                                  ([&]() {
                        VL_NULL_CHECK(__Vtask___VforkTask_0__26____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 115)
                                                   ->__VnoInFunc_status(vlSymsp, __Vtask_status__27__Vfuncout);
                    }(), __Vtask_status__27__Vfuncout));
            __VdynTrigger_hcbe693c9__0 = this->__Vtrigprevexpr_hb998f206__0;
            vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_hcbe693c9__0);
        }
        co_await vlSymsp->TOP.__VdynSched.resumption(
                                                     vlProcess, 
                                                     "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvme_fifo_pkg::uvme_fifo_prdr_c.__Vtask___VforkTask_0__26____VforkParent.(uvme_fifo_pkg::uvme_fifo_prdr_c.__Vtask_status__27__Vfuncout); , ); ))", 
                                                     "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 
                                                     115);
    }
    co_await this->__VnoInFunc_process_write(vlProcess, vlSymsp, __Vtask___VforkTask_0__26__wr_tr);
    vlProcess->state(VlProcess::FINISHED);
    co_return;}

VlCoroutine uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_process_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> tr) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_process_write\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__34__Vfuncout;
    __Vfunc_uvm_report_enabled__34__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__36__Vfuncout;
    __Vfunc_uvm_report_enabled__36__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    while (true) {
        CData/*0:0*/ __VdynTrigger_h30158188__0;
        __VdynTrigger_h30158188__0 = 0;
        __VdynTrigger_h30158188__0 = 0U;
        this->__Vtrigprevexpr_h15e9d615__0 = VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 129)
                                                           ->__PVT__wr_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 129)
            ->clk;
        while ((1U & (~ (IData)(__VdynTrigger_h30158188__0)))) {
            co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                         vlProcess, 
                                                         "@(posedge uvme_fifo_pkg::uvme_fifo_prdr_c.cntxt.wr_vif.clk)", 
                                                         "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 
                                                         129);
            __VdynTrigger_h30158188__0 = (VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 129)
                                                        ->__PVT__wr_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 129)
                                          ->clk & (~ (IData)(this->__Vtrigprevexpr_h15e9d615__0)));
            vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_h30158188__0);
            this->__Vtrigprevexpr_h15e9d615__0 = VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 129)
                                                               ->__PVT__wr_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 129)
                ->clk;
        }
        co_await vlSymsp->TOP.__VdynSched.resumption(
                                                     vlProcess, 
                                                     "@(posedge uvme_fifo_pkg::uvme_fifo_prdr_c.cntxt.wr_vif.clk)", 
                                                     "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 
                                                     129);
        if (VL_LTS_III(32, 0U, this->__PVT__wr_queue.size())) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "WR_PRDR"s, __Vfunc_uvm_report_enabled__34__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__34__Vfuncout))) {
                this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "WR_PRDR"s, "queue is not empty so process_write"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x00000083U, ""s, 1U);
            }
            tr = this->__PVT__wr_queue.pop_front();
            if (VL_GTES_III(32, this->__PVT__fifo.size(), this->__PVT__fifo_depth)) {
                VL_NULL_CHECK(tr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 134)->__PVT__w_full = 1U;
            } else {
                VL_NULL_CHECK(tr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 137)->__PVT__w_full = 0U;
                if (VL_NULL_CHECK(tr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 138)
                    ->__PVT__w_en) {
                    this->__PVT__fifo.push_back(VL_NULL_CHECK(tr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 139)
                                                ->__PVT__w_data);
                }
            }
            if ((VlNull{} == tr)) {
                if ((0U != ([&]() {
                                this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "WR_PRDR_null"s, __Vfunc_uvm_report_enabled__36__Vfuncout);
                            }(), __Vfunc_uvm_report_enabled__36__Vfuncout))) {
                    this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "WR_PRDR_null"s, "tr is null"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x0000008fU, ""s, 1U);
                }
            } else {
                VL_NULL_CHECK(this->__PVT__wr_output_port, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 146)->__VnoInFunc_write(vlProcess, vlSymsp, tr);
            }
        }
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_process_read(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> tr) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_process_read\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__39__Vfuncout;
    __Vfunc_uvm_report_enabled__39__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__41__Vfuncout;
    __Vfunc_uvm_report_enabled__41__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    while (true) {
        CData/*0:0*/ __VdynTrigger_hf514b35c__0;
        __VdynTrigger_hf514b35c__0 = 0;
        __VdynTrigger_hf514b35c__0 = 0U;
        this->__Vtrigprevexpr_hceeb07e9__0 = VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 159)
                                                           ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 159)
            ->clk;
        while ((1U & (~ (IData)(__VdynTrigger_hf514b35c__0)))) {
            co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                         vlProcess, 
                                                         "@(posedge uvme_fifo_pkg::uvme_fifo_prdr_c.cntxt.rd_vif.clk)", 
                                                         "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 
                                                         159);
            __VdynTrigger_hf514b35c__0 = (VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 159)
                                                        ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 159)
                                          ->clk & (~ (IData)(this->__Vtrigprevexpr_hceeb07e9__0)));
            vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_hf514b35c__0);
            this->__Vtrigprevexpr_hceeb07e9__0 = VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 159)
                                                               ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 159)
                ->clk;
        }
        co_await vlSymsp->TOP.__VdynSched.resumption(
                                                     vlProcess, 
                                                     "@(posedge uvme_fifo_pkg::uvme_fifo_prdr_c.cntxt.rd_vif.clk)", 
                                                     "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 
                                                     159);
        if (VL_LTS_III(32, 0U, this->__PVT__rd_queue.size())) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "RD_PRDR"s, __Vfunc_uvm_report_enabled__39__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__39__Vfuncout))) {
                this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "RD_PRDR"s, "queue is not empty so process_read"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x000000a2U, ""s, 1U);
            }
            tr = this->__PVT__rd_queue.pop_front();
            if (VL_GTES_III(32, 0U, this->__PVT__fifo.size())) {
                VL_NULL_CHECK(tr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 165)->__PVT__r_empty = 1U;
            } else {
                VL_NULL_CHECK(tr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 168)->__PVT__r_empty = 0U;
                if (VL_NULL_CHECK(tr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 169)
                    ->__PVT__r_en) {
                    VL_NULL_CHECK(tr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 170)->__PVT__r_data 
                        = this->__PVT__fifo.pop_front();
                }
            }
            if ((VlNull{} == tr)) {
                if ((0U != ([&]() {
                                this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "RD_PRDR_null"s, __Vfunc_uvm_report_enabled__41__Vfuncout);
                            }(), __Vfunc_uvm_report_enabled__41__Vfuncout))) {
                    this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "RD_PRDR_null"s, "tr is null"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh"s, 0x000000aeU, ""s, 1U);
                }
            } else {
                VL_NULL_CHECK(this->__PVT__rd_output_port, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_prdr.svh", 177)->__VnoInFunc_write(vlProcess, vlSymsp, tr);
            }
        }
    }
    co_return;}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_write_wr_input(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> tr) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_write_wr_input\n"); );
    // Body
    this->__PVT__wr_queue.push_back(tr);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_write_rd_input(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> tr) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_write_rd_input\n"); );
    // Body
    this->__PVT__rd_queue.push_back(tr);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__45__Vfuncout;
    __Vfunc___VBasicRand__45__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__45__Vfuncout);
            }(), __Vfunc___VBasicRand__45__Vfuncout));
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__fifo.atDefault() = VL_SCOPED_RAND_RESET_I(8, 5418287804849337199ULL, 6099733058761723038ull);
    __PVT__fifo_depth = 0;
    __Vtrigprevexpr_hb998f206__0 = 0;
    __Vtrigprevexpr_hb7c3d9d2__0 = 0;
    __Vtrigprevexpr_h15e9d615__0 = 0;
    __Vtrigprevexpr_hceeb07e9__0 = 0;
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += "cfg:" + VL_TO_STRING(__PVT__cfg);
    out += ", cntxt:" + VL_TO_STRING(__PVT__cntxt);
    out += ", wr_input_imp:" + VL_TO_STRING(__PVT__wr_input_imp);
    out += ", rd_input_imp:" + VL_TO_STRING(__PVT__rd_input_imp);
    out += ", wr_output_port:" + VL_TO_STRING(__PVT__wr_output_port);
    out += ", rd_output_port:" + VL_TO_STRING(__PVT__rd_output_port);
    out += ", wr_queue:" + VL_TO_STRING(__PVT__wr_queue);
    out += ", rd_queue:" + VL_TO_STRING(__PVT__rd_queue);
    out += ", fifo:" + VL_TO_STRING(__PVT__fifo);
    out += ", fifo_depth:" + VL_TO_STRING(__PVT__fifo_depth);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::to_string_middle();
    return (out);
}
