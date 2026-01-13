// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi177> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi177> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi177__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvma_rd_mon_c"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi177> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi177__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvma_rd_mon_c"s;
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

VlCoroutine uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc_mon_one_item(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> tr) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc_mon_one_item\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__2__Vfuncout;
    __Vfunc_uvm_report_enabled__2__Vfuncout = 0;
    CData/*0:0*/ __Vtrigprevexpr_h445a192b__0;
    __Vtrigprevexpr_h445a192b__0 = 0;
    // Body
    VL_KEEP_THIS;
    CData/*0:0*/ __VdynTrigger_h42a5bbfe__0;
    __VdynTrigger_h42a5bbfe__0 = 0;
    __VdynTrigger_h42a5bbfe__0 = 0U;
    __Vtrigprevexpr_h445a192b__0 = VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 184)
                                                 ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 184)
        ->clk;
    while ((1U & (~ (IData)(__VdynTrigger_h42a5bbfe__0)))) {
        co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                     vlProcess, 
                                                     "@(posedge uvma_wr_rd_pkg::uvma_wr_rd_base_mon_c__Tz155.cntxt.rd_vif.clk)", 
                                                     "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 
                                                     184);
        __VdynTrigger_h42a5bbfe__0 = (VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 184)
                                                    ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 184)
                                      ->clk & (~ (IData)(__Vtrigprevexpr_h445a192b__0)));
        vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_h42a5bbfe__0);
        __Vtrigprevexpr_h445a192b__0 = VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 184)
                                                     ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 184)
            ->clk;
    }
    co_await vlSymsp->TOP.__VdynSched.resumption(vlProcess, 
                                                 "@(posedge uvma_wr_rd_pkg::uvma_wr_rd_base_mon_c__Tz155.cntxt.rd_vif.clk)", 
                                                 "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 
                                                 184);
    {
        while (true) {
            CData/*0:0*/ __VdynTrigger_h42a5bbfe__1;
            __VdynTrigger_h42a5bbfe__1 = 0;
            __VdynTrigger_h42a5bbfe__1 = 0U;
            this->__Vtrigprevexpr_h445a192b__1 = VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 187)
                                                               ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 187)
                ->clk;
            while ((1U & (~ (IData)(__VdynTrigger_h42a5bbfe__1)))) {
                co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                             vlProcess, 
                                                             "@(posedge uvma_wr_rd_pkg::uvma_wr_rd_base_mon_c__Tz155.cntxt.rd_vif.clk)", 
                                                             "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 
                                                             187);
                __VdynTrigger_h42a5bbfe__1 = (VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 187)
                                                            ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 187)
                                              ->clk 
                                              & (~ (IData)(this->__Vtrigprevexpr_h445a192b__1)));
                vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_h42a5bbfe__1);
                this->__Vtrigprevexpr_h445a192b__1 
                    = VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 187)
                                    ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 187)
                    ->clk;
            }
            co_await vlSymsp->TOP.__VdynSched.resumption(
                                                         vlProcess, 
                                                         "@(posedge uvma_wr_rd_pkg::uvma_wr_rd_base_mon_c__Tz155.cntxt.rd_vif.clk)", 
                                                         "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 
                                                         187);
            if (VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 188)
                              ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 188)
                ->en) {
                goto __Vlabel0;
            }
        }
        __Vlabel0: ;
    }
    VL_NULL_CHECK(tr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 191)->__PVT__r_data 
        = VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 191)
                        ->__PVT__rd_vif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh", 191)
        ->data;
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "RD_MON"s, __Vfunc_uvm_report_enabled__2__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__2__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "RD_MON"s, " :: mon_one_item"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_mon.svh"s, 0x000000c0U, ""s, 1U);
    }
    co_return;}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__5__Vfuncout;
    __Vfunc___VBasicRand__5__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__5__Vfuncout);
            }(), __Vfunc___VBasicRand__5__Vfuncout));
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __Vtrigprevexpr_h445a192b__1 = 0;
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_mon_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155::to_string_middle();
    return (out);
}
