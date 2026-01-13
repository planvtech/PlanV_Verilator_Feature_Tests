// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi89> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi89> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi89__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvma_wr_rd_agent_c#(SEQ_ITEM)"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi89> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi89__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvma_wr_rd_agent_c#(SEQ_ITEM)"s;
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_agent(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_build_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__3__Vfuncout;
    __Vfunc_uvm_report_enabled__3__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__9__Vfuncout;
    __Vfunc_uvm_report_enabled__9__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_agent::__VnoInFunc_build_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "AGENT"s, __Vfunc_uvm_report_enabled__3__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__3__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "AGENT"s, "Entered build phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x00000042U, ""s, 1U);
    }
    this->__VnoInFunc_get_and_set_cfg(vlProcess, vlSymsp);
    this->__VnoInFunc_get_and_set_cntxt(vlProcess, vlSymsp);
    this->__VnoInFunc_retrieve_vifs(vlProcess, vlSymsp);
    this->__VnoInFunc_create_components(vlProcess, vlSymsp);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "AGENT"s, __Vfunc_uvm_report_enabled__9__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__9__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "AGENT"s, "Exiting build phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x00000047U, ""s, 1U);
    }
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_connect_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_connect_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__12__Vfuncout;
    __Vfunc_uvm_report_enabled__12__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__17__Vfuncout;
    __Vfunc_uvm_report_enabled__17__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_connect_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "AGENT"s, __Vfunc_uvm_report_enabled__12__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__12__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "AGENT"s, "Entered connect phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x00000050U, ""s, 1U);
    }
    this->__VnoInFunc_connect_sequencer_and_driver(vlProcess, vlSymsp);
    this->__VnoInFunc_connect_analysis_ports(vlProcess, vlSymsp);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "AGENT"s, __Vfunc_uvm_report_enabled__17__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__17__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "AGENT"s, "Exiting connect phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x0000005dU, ""s, 1U);
    }
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_get_and_set_cfg(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_get_and_set_cfg\n"); );
    // Locals
    CData/*0:0*/ __Vtask_get__19__Vfuncout;
    __Vtask_get__19__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cfg_c> __Vtask_get__19__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__20__Vfuncout;
    __Vfunc_uvm_report_enabled__20__Vfuncout = 0;
    // Body
    __Vtask_get__19__value = this->__PVT__cfg;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz158__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>{this}, ""s, "cfg"s, __Vtask_get__19__value, __Vtask_get__19__Vfuncout);
    this->__PVT__cfg = __Vtask_get__19__value;
    if ((VlNull{} == this->__PVT__cfg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "CFG"s, __Vfunc_uvm_report_enabled__20__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__20__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "CFG"s, "cfg is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x00000066U, ""s, 1U);
        }
    } else {
        vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz158__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>{this}, "*"s, "cfg"s, this->__PVT__cfg);
    }
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_get_and_set_cntxt(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_get_and_set_cntxt\n"); );
    // Locals
    CData/*0:0*/ __Vtask_get__23__Vfuncout;
    __Vtask_get__23__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c> __Vtask_get__23__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__24__Vfuncout;
    __Vfunc_uvm_report_enabled__24__Vfuncout = 0;
    // Body
    __Vtask_get__23__value = this->__PVT__cntxt;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz159__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>{this}, ""s, "cntxt"s, __Vtask_get__23__value, __Vtask_get__23__Vfuncout);
    this->__PVT__cntxt = __Vtask_get__23__value;
    if ((VlNull{} == this->__PVT__cntxt)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "CNTXT"s, __Vfunc_uvm_report_enabled__24__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__24__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "CNTXT"s, "cntxt is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x00000073U, ""s, 1U);
        }
    } else {
        vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz159__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>{this}, "*"s, "cntxt"s, this->__PVT__cntxt);
    }
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_retrieve_vifs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_retrieve_vifs\n"); );
    // Locals
    CData/*0:0*/ __Vfunc_get__27__Vfuncout;
    __Vfunc_get__27__Vfuncout = 0;
    uvmt_fifo_tb_uvma_wr_if* __Vfunc_get__27__value;
    __Vfunc_get__27__value = nullptr;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__28__Vfuncout;
    __Vfunc_uvm_report_enabled__28__Vfuncout = 0;
    CData/*0:0*/ __Vfunc_get__30__Vfuncout;
    __Vfunc_get__30__Vfuncout = 0;
    uvmt_fifo_tb_uvma_rd_if* __Vfunc_get__30__value;
    __Vfunc_get__30__value = nullptr;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__31__Vfuncout;
    __Vfunc_uvm_report_enabled__31__Vfuncout = 0;
    // Body
    if ((1U & (~ ([&]() {
                        __Vfunc_get__27__value = VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 126)
                            ->__PVT__wr_vif;
                        vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz2__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>{this}, ""s, "wr_vif"s, __Vfunc_get__27__value, __Vfunc_get__27__Vfuncout);
                        VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 126)
                  ->__PVT__wr_vif = __Vfunc_get__27__value;
                    }(), (IData)(__Vfunc_get__27__Vfuncout))))) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "WR_VIF"s, __Vfunc_uvm_report_enabled__28__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__28__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "WR_VIF"s, "wr_vif is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x0000007fU, ""s, 1U);
        }
    }
    if ((1U & (~ ([&]() {
                        __Vfunc_get__30__value = VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 130)
                            ->__PVT__rd_vif;
                        vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz3__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>{this}, ""s, "rd_vif"s, __Vfunc_get__30__value, __Vfunc_get__30__Vfuncout);
                        VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 130)
                  ->__PVT__rd_vif = __Vfunc_get__30__value;
                    }(), (IData)(__Vfunc_get__30__Vfuncout))))) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "RD_VIF"s, __Vfunc_uvm_report_enabled__31__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__31__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "RD_VIF"s, "rd_vif is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x00000083U, ""s, 1U);
        }
    }
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_create_components(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_create_components\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi175> __Vfunc_get_type__34__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi177> __Vfunc_get_type__36__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi179> __Vfunc_get_type__38__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__39__Vfuncout;
    __Vfunc_uvm_report_enabled__39__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi174> __Vfunc_get_type__42__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi176> __Vfunc_get_type__44__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi178> __Vfunc_get_type__46__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_drv_c__Tz155> __Vfunc_create__47__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz155> __Vfunc_create__48__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz155> __Vfunc_create__49__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__50__Vfuncout;
    __Vfunc_uvm_report_enabled__50__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__52__Vfuncout;
    __Vfunc_uvm_report_enabled__52__Vfuncout = 0;
    std::string __Vtask_get_type_name__54__Vfuncout;
    std::string __Vtemp_1;
    // Body
    if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 139)
        ->__PVT__wr_or_rd) {
        if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 144)
            ->__PVT__wr_or_rd) {
            vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi118__Vclpkg.__VnoInFunc_set_type_override(vlProcess, vlSymsp, 
                                                                                ([&]() {
                        vlSymsp->TOP__uvma_wr_rd_pkg__03a__03auvma_rd_drv_c__Vclpkg.__VnoInFunc_get_type(vlSymsp, __Vfunc_get_type__34__Vfuncout);
                    }(), __Vfunc_get_type__34__Vfuncout), 1U);
            vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi119__Vclpkg.__VnoInFunc_set_type_override(vlProcess, vlSymsp, 
                                                                                ([&]() {
                        vlSymsp->TOP__uvma_wr_rd_pkg__03a__03auvma_rd_mon_c__Vclpkg.__VnoInFunc_get_type(vlSymsp, __Vfunc_get_type__36__Vfuncout);
                    }(), __Vfunc_get_type__36__Vfuncout), 1U);
            vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi91__Vclpkg.__VnoInFunc_set_type_override(vlProcess, vlSymsp, 
                                                                                ([&]() {
                        vlSymsp->TOP__uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c__Vclpkg.__VnoInFunc_get_type(vlSymsp, __Vfunc_get_type__38__Vfuncout);
                    }(), __Vfunc_get_type__38__Vfuncout), 1U);
        } else if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "AGENT"s, __Vfunc_uvm_report_enabled__39__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__39__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "AGENT"s, "cfg.wr_or_rd is not WR or RD"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x00000096U, ""s, 1U);
        }
    } else {
        vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi118__Vclpkg.__VnoInFunc_set_type_override(vlProcess, vlSymsp, 
                                                                                ([&]() {
                    vlSymsp->TOP__uvma_wr_rd_pkg__03a__03auvma_wr_drv_c__Vclpkg.__VnoInFunc_get_type(vlSymsp, __Vfunc_get_type__42__Vfuncout);
                }(), __Vfunc_get_type__42__Vfuncout), 1U);
        vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi119__Vclpkg.__VnoInFunc_set_type_override(vlProcess, vlSymsp, 
                                                                                ([&]() {
                    vlSymsp->TOP__uvma_wr_rd_pkg__03a__03auvma_wr_mon_c__Vclpkg.__VnoInFunc_get_type(vlSymsp, __Vfunc_get_type__44__Vfuncout);
                }(), __Vfunc_get_type__44__Vfuncout), 1U);
        vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi91__Vclpkg.__VnoInFunc_set_type_override(vlProcess, vlSymsp, 
                                                                                ([&]() {
                    vlSymsp->TOP__uvma_wr_rd_pkg__03a__03auvma_wr_sqr_c__Vclpkg.__VnoInFunc_get_type(vlSymsp, __Vfunc_get_type__46__Vfuncout);
                }(), __Vfunc_get_type__46__Vfuncout), 1U);
    }
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi118__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "drv"s, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>{this}, ""s, __Vfunc_create__47__Vfuncout);
    this->__PVT__drv = __Vfunc_create__47__Vfuncout;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi91__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "sqr"s, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>{this}, ""s, __Vfunc_create__48__Vfuncout);
    this->__PVT__sqr = __Vfunc_create__48__Vfuncout;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi119__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "mon"s, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>{this}, ""s, __Vfunc_create__49__Vfuncout);
    this->__PVT__mon = __Vfunc_create__49__Vfuncout;
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "AGENT"s, __Vfunc_uvm_report_enabled__50__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__50__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "AGENT"s, "type of mon := class{}uvma_wr_rd_base_mon_c__Tz155"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x0000009cU, ""s, 1U);
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "AGENT"s, __Vfunc_uvm_report_enabled__52__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__52__Vfuncout))) {
        __Vtemp_1 = ([&]() {
                VL_NULL_CHECK(this->__PVT__mon, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 157)
                     ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__54__Vfuncout);
            }(), __Vtask_get_type_name__54__Vfuncout);
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "AGENT"s, VL_SFORMATF_N_NX("type of mon := %@",0,
                                                                                -1,
                                                                                &(__Vtemp_1)) , 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x0000009dU, ""s, 1U);
    }
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_connect_sequencer_and_driver(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_connect_sequencer_and_driver\n"); );
    // Body
    VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__drv, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 167)
                  ->__PVT__seq_item_port, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 167)->__VnoInFunc_connect(vlProcess, vlSymsp, VL_NULL_CHECK(this->__PVT__sqr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 167)
                                                                                ->__PVT__seq_item_export);
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_connect_analysis_ports(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_connect_analysis_ports\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__56__Vfuncout;
    __Vfunc_uvm_report_enabled__56__Vfuncout = 0;
    // Body
    if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 174)
        ->__PVT__is_active) {
        this->__PVT__drv_ap = VL_NULL_CHECK(this->__PVT__drv, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 175)
            ->__PVT__ap;
        this->__PVT__mon_ap = VL_NULL_CHECK(this->__PVT__mon, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 176)
            ->__PVT__ap;
    } else if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 178)
               ->__PVT__is_active) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "AGENT"s, __Vfunc_uvm_report_enabled__56__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__56__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "AGENT"s, "cfg.is_active is not UVM_ACTIVE or UVM_PASSIVE"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh"s, 0x000000b6U, ""s, 1U);
        }
    } else {
        this->__PVT__mon_ap = VL_NULL_CHECK(this->__PVT__mon, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_agent.svh", 179)
            ->__PVT__ap;
    }
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__59__Vfuncout;
    __Vfunc___VBasicRand__59__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__59__Vfuncout);
            }(), __Vfunc___VBasicRand__59__Vfuncout));
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                              uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155::to_string_middle\n"); );
    // Body
    std::string out;
    out += "cfg:" + VL_TO_STRING(__PVT__cfg);
    out += ", cntxt:" + VL_TO_STRING(__PVT__cntxt);
    out += ", drv:" + VL_TO_STRING(__PVT__drv);
    out += ", mon:" + VL_TO_STRING(__PVT__mon);
    out += ", sqr:" + VL_TO_STRING(__PVT__sqr);
    out += ", drv_ap:" + VL_TO_STRING(__PVT__drv_ap);
    out += ", mon_ap:" + VL_TO_STRING(__PVT__mon_ap);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_agent::to_string_middle();
    return (out);
}
