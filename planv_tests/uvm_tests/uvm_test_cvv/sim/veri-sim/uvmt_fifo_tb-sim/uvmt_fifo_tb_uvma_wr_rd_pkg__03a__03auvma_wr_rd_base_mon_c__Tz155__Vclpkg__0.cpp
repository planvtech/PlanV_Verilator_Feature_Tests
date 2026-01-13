// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi119> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi119> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi119__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvma_wr_rd_base_mon_c#(SEQ_ITEM)"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi119> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi119__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvma_wr_rd_base_mon_c#(SEQ_ITEM)"s;
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_monitor(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_build_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__3__Vfuncout;
    __Vfunc_uvm_report_enabled__3__Vfuncout = 0;
    CData/*0:0*/ __Vtask_get__5__Vfuncout;
    __Vtask_get__5__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cfg_c> __Vtask_get__5__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__6__Vfuncout;
    __Vfunc_uvm_report_enabled__6__Vfuncout = 0;
    CData/*0:0*/ __Vtask_get__8__Vfuncout;
    __Vtask_get__8__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c> __Vtask_get__8__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__9__Vfuncout;
    __Vfunc_uvm_report_enabled__9__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__12__Vfuncout;
    __Vfunc_uvm_report_enabled__12__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_build_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "MON"s, __Vfunc_uvm_report_enabled__3__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__3__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "MON"s, "Entered build_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x00000035U, ""s, 1U);
    }
    __Vtask_get__5__value = this->__PVT__cfg;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz158__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155>{this}, ""s, "cfg"s, __Vtask_get__5__value, __Vtask_get__5__Vfuncout);
    this->__PVT__cfg = __Vtask_get__5__value;
    if ((VlNull{} == this->__PVT__cfg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "CFG"s, __Vfunc_uvm_report_enabled__6__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__6__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "CFG"s, "cfg is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x00000039U, ""s, 1U);
        }
    }
    __Vtask_get__8__value = this->__PVT__cntxt;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz159__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155>{this}, ""s, "cntxt"s, __Vtask_get__8__value, __Vtask_get__8__Vfuncout);
    this->__PVT__cntxt = __Vtask_get__8__value;
    if ((VlNull{} == this->__PVT__cntxt)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "CNTXT"s, __Vfunc_uvm_report_enabled__9__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__9__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "CNTXT"s, "cntxt is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x0000003eU, ""s, 1U);
        }
    }
    this->__PVT__ap = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz155, vlProcess, vlSymsp, "ap"s, 
                             VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155>{this});
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "MON"s, __Vfunc_uvm_report_enabled__12__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__12__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "MON"s, "Exiting build_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x00000043U, ""s, 1U);
    }
}

VlCoroutine uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_run_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_run_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__16__Vfuncout;
    __Vfunc_uvm_report_enabled__16__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__18__Vfuncout;
    __Vfunc_uvm_report_enabled__18__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__20__Vfuncout;
    __Vfunc_uvm_report_enabled__20__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vfunc_self__22__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__32__Vfuncout;
    __Vfunc_uvm_report_enabled__32__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk2__DOT____VforkParent;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03a__VDynScope_34> __VDynScope_run_phase_0;
    __VDynScope_run_phase_0 = VL_NEW(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03a__VDynScope_34, vlSymsp);
    co_await uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_run_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "MON"s, __Vfunc_uvm_report_enabled__16__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__16__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "MON"s, "Entered run_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x0000004eU, ""s, 1U);
    }
    if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 80)
        ->__PVT__enabled) {
        if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 81)
            ->__PVT__wr_or_rd) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "MON"s, __Vfunc_uvm_report_enabled__18__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__18__Vfuncout))) {
                this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "MON"s, "RD_Monitor is enabled in Run Phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x00000055U, ""s, 1U);
            }
        } else if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "MON"s, __Vfunc_uvm_report_enabled__20__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__20__Vfuncout))) {
            this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "MON"s, "WR_Monitor is enabled in Run Phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x00000052U, ""s, 1U);
        }
        vlSymsp->TOP__std__03a__03aprocess__Vclpkg.__VnoInFunc_self(vlProcess, vlSymsp, __Vfunc_self__22__Vfuncout);
        unnamedblk2__DOT____VforkParent = __Vfunc_self__22__Vfuncout;
        this->__VnoInFunc_run_phase____Vfork_1__0(std::make_shared<VlProcess>(vlProcess), vlSymsp, __VDynScope_run_phase_0, unnamedblk2__DOT____VforkParent);
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "MON"s, __Vfunc_uvm_report_enabled__32__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__32__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "MON"s, "Exiting run_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x00000073U, ""s, 1U);
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_run_phase____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03a__VDynScope_34> __VDynScope_run_phase_0, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk2__DOT____VforkParent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_run_phase____Vfork_1__0\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vtask___VforkTask_0__23____VforkParent;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03a__VDynScope_34> __Vtask___VforkTask_0__23____VDynScope_run_phase_0;
    IData/*31:0*/ __Vtask_status__24__Vfuncout;
    __Vtask_status__24__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__27__Vfuncout;
    __Vfunc_uvm_report_enabled__27__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__29__Vfuncout;
    __Vfunc_uvm_report_enabled__29__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    __Vtask___VforkTask_0__23____VDynScope_run_phase_0 
        = __VDynScope_run_phase_0;
    __Vtask___VforkTask_0__23____VforkParent = unnamedblk2__DOT____VforkParent;
    if ((1U == ([&]() {
                    VL_NULL_CHECK(__Vtask___VforkTask_0__23____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 88)
                ->__VnoInFunc_status(vlSymsp, __Vtask_status__24__Vfuncout);
                }(), __Vtask_status__24__Vfuncout))) {
        CData/*0:0*/ __VdynTrigger_h944e4535__0;
        __VdynTrigger_h944e4535__0 = 0;
        __VdynTrigger_h944e4535__0 = 0U;
        while ((1U & (~ (IData)(__VdynTrigger_h944e4535__0)))) {
            co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                         vlProcess, 
                                                         "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvma_wr_rd_pkg::uvma_wr_rd_base_mon_c__Tz155.__Vtask___VforkTask_0__23____VforkParent.(uvma_wr_rd_pkg::uvma_wr_rd_base_mon_c__Tz155.__Vtask_status__24__Vfuncout); , ); ))", 
                                                         "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 
                                                         88);
            this->__Vtrigprevexpr_h7221a25a__0 = (1U 
                                                  != 
                                                  ([&]() {
                        VL_NULL_CHECK(__Vtask___VforkTask_0__23____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 88)
                                                   ->__VnoInFunc_status(vlSymsp, __Vtask_status__24__Vfuncout);
                    }(), __Vtask_status__24__Vfuncout));
            __VdynTrigger_h944e4535__0 = this->__Vtrigprevexpr_h7221a25a__0;
            vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_h944e4535__0);
        }
        co_await vlSymsp->TOP.__VdynSched.resumption(
                                                     vlProcess, 
                                                     "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvma_wr_rd_pkg::uvma_wr_rd_base_mon_c__Tz155.__Vtask___VforkTask_0__23____VforkParent.(uvma_wr_rd_pkg::uvma_wr_rd_base_mon_c__Tz155.__Vtask_status__24__Vfuncout); , ); ))", 
                                                     "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 
                                                     88);
    }
    while (true) {
        VL_NULL_CHECK(__Vtask___VforkTask_0__23____VDynScope_run_phase_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 92)->__PVT__tr 
            = VL_NEW(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c, vlProcess, vlSymsp, "tr"s);
        co_await this->__VnoInFunc_mon_one_item(vlProcess, vlSymsp, VL_NULL_CHECK(__Vtask___VforkTask_0__23____VDynScope_run_phase_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 96)
                                                ->__PVT__tr);
        if ((VlNull{} == VL_NULL_CHECK(__Vtask___VforkTask_0__23____VDynScope_run_phase_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 97)
             ->__PVT__tr)) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "MON_null"s, __Vfunc_uvm_report_enabled__27__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__27__Vfuncout))) {
                this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "MON_null"s, "tr is null"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x00000062U, ""s, 1U);
            }
        } else {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "MON_sb"s, __Vfunc_uvm_report_enabled__29__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__29__Vfuncout))) {
                this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "MON_sb"s, "tr is not null"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x00000065U, ""s, 1U);
            }
            VL_NULL_CHECK(this->__PVT__ap, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 102)->__VnoInFunc_write(vlProcess, vlSymsp, VL_NULL_CHECK(__Vtask___VforkTask_0__23____VDynScope_run_phase_0, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 102)
                                                                                ->__PVT__tr);
        }
    }
    vlProcess->state(VlProcess::FINISHED);
    co_return;}

VlCoroutine uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_mon_one_item(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> tr) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_mon_one_item\n"); );
    // Body
    VL_KEEP_THIS;
    co_return;}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__35__Vfuncout;
    __Vfunc___VBasicRand__35__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__35__Vfuncout);
            }(), __Vfunc___VBasicRand__35__Vfuncout));
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __Vtrigprevexpr_h7221a25a__0 = 0;
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::to_string_middle\n"); );
    // Body
    std::string out;
    out += "cfg:" + VL_TO_STRING(__PVT__cfg);
    out += ", cntxt:" + VL_TO_STRING(__PVT__cntxt);
    out += ", ap:" + VL_TO_STRING(__PVT__ap);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_monitor::to_string_middle();
    return (out);
}
