// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi72> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi72> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi72__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvme_fifo_env_c"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi72> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi72__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvme_fifo_env_c"s;
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_env(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_build_phase\n"); );
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
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c> __Vfunc_create__11__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__19__Vfuncout;
    __Vfunc_uvm_report_enabled__19__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_build_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "ENV"s, __Vfunc_uvm_report_enabled__3__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__3__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "ENV"s, "Entered build phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x0000004aU, ""s, 1U);
    }
    __Vtask_get__5__value = this->__PVT__cfg;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz146__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, ""s, "cfg"s, __Vtask_get__5__value, __Vtask_get__5__Vfuncout);
    this->__PVT__cfg = __Vtask_get__5__value;
    if ((VlNull{} == this->__PVT__cfg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "ENV_CFG"s, __Vfunc_uvm_report_enabled__6__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__6__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "ENV_CFG"s, "cfg is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x0000004eU, ""s, 1U);
        }
    }
    if (VL_UNLIKELY((VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 81)
                     ->__PVT__enabled))) {
        VL_WRITEF_NX("ENV: cfg is enabled in build_phase.\n",0);
        __Vtask_get__8__value = this->__PVT__cntxt;
        vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz147__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, ""s, "cntxt"s, __Vtask_get__8__value, __Vtask_get__8__Vfuncout);
        this->__PVT__cntxt = __Vtask_get__8__value;
        if ((VlNull{} == this->__PVT__cntxt)) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "CNTXT"s, __Vfunc_uvm_report_enabled__9__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__9__Vfuncout))) {
                this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "CNTXT"s, "cntxt is null"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x00000055U, ""s, 1U);
            }
            vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi71__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "cntxt"s, VlNull{}, ""s, __Vfunc_create__11__Vfuncout);
            this->__PVT__cntxt = __Vfunc_create__11__Vfuncout;
        }
        this->__VnoInFunc_retrieve_vifs(vlProcess, vlSymsp);
        this->__VnoInFunc_assign_cfg(vlProcess, vlSymsp);
        this->__VnoInFunc_assign_cntxt(vlProcess, vlSymsp);
        this->__VnoInFunc_create_agents(vlProcess, vlSymsp);
        this->__VnoInFunc_create_env_components(vlProcess, vlSymsp);
        if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 95)
            ->__PVT__is_active) {
            this->__VnoInFunc_create_vsequencer(vlProcess, vlSymsp);
        }
        if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 99)
            ->__PVT__cov_model_enabled) {
            this->__VnoInFunc_create_cov_model(vlSymsp);
        }
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "ENV"s, __Vfunc_uvm_report_enabled__19__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__19__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "ENV"s, "Exiting build phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x00000068U, ""s, 1U);
    }
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_connect_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_connect_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__22__Vfuncout;
    __Vfunc_uvm_report_enabled__22__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__24__Vfuncout;
    __Vfunc_uvm_report_enabled__24__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__32__Vfuncout;
    __Vfunc_uvm_report_enabled__32__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_connect_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "ENV"s, __Vfunc_uvm_report_enabled__22__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__22__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "ENV"s, "Entered connect phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x00000071U, ""s, 1U);
    }
    if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 115)
        ->__PVT__enabled) {
        if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 117)
            ->__PVT__scoreboard_enabled) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "ENV"s, __Vfunc_uvm_report_enabled__24__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__24__Vfuncout))) {
                this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "ENV"s, "scoreboard_enabled is true, connecting predictor and scoreboard."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x00000076U, ""s, 1U);
            }
            this->__VnoInFunc_connect_predictor(vlProcess, vlSymsp);
            this->__VnoInFunc_connect_scoreboard(vlProcess, vlSymsp);
            VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__predictor, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 121)
                          ->__PVT__wr_output_port, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 121)->__VnoInFunc_connect(vlProcess, vlSymsp, VL_NULL_CHECK(this->__PVT__scoreboard, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 121)
                                                                                ->__PVT__wr_exp_imp);
            VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__predictor, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 122)
                          ->__PVT__rd_output_port, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 122)->__VnoInFunc_connect(vlProcess, vlSymsp, VL_NULL_CHECK(this->__PVT__scoreboard, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 122)
                                                                                ->__PVT__rd_exp_imp);
        }
        if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 125)
            ->__PVT__is_active) {
            this->__VnoInFunc_assemble_vsequencer(vlSymsp);
        }
        if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 129)
            ->__PVT__cov_model_enabled) {
            this->__VnoInFunc_connect_cov_model(vlSymsp);
        }
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "ENV"s, __Vfunc_uvm_report_enabled__32__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__32__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "ENV"s, "Exiting connect phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x00000086U, ""s, 1U);
    }
}

VlCoroutine uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_run_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_run_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__35__Vfuncout;
    __Vfunc_uvm_report_enabled__35__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c> __Vfunc_create__37__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__39__Vfuncout;
    __Vfunc_uvm_report_enabled__39__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c> random_vseq;
    co_await uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_run_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "ENV"s, __Vfunc_uvm_report_enabled__35__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__35__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "ENV"s, "Entered run phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x00000091U, ""s, 1U);
    }
    if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 147)
        ->__PVT__is_active) {
        vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi82__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "random_vseq"s, VlNull{}, ""s, __Vfunc_create__37__Vfuncout);
        random_vseq = __Vfunc_create__37__Vfuncout;
        co_await VL_NULL_CHECK(random_vseq, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 149)->__VnoInFunc_start(vlProcess, vlSymsp, this->__PVT__vsequencer, VlNull{}, 0xffffffffU, 1U);
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "ENV"s, __Vfunc_uvm_report_enabled__39__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__39__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "ENV"s, "Exiting run phase."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x00000098U, ""s, 1U);
    }
    co_return;}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_end_of_elaboration_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_end_of_elaboration_phase\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_end_of_elaboration_phase(vlProcess, vlSymsp, phase);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_retrieve_vifs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_retrieve_vifs\n"); );
    // Locals
    CData/*0:0*/ __Vfunc_get__42__Vfuncout;
    __Vfunc_get__42__Vfuncout = 0;
    uvmt_fifo_tb_uvma_wr_if* __Vfunc_get__42__value;
    __Vfunc_get__42__value = nullptr;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__43__Vfuncout;
    __Vfunc_uvm_report_enabled__43__Vfuncout = 0;
    CData/*0:0*/ __Vfunc_get__45__Vfuncout;
    __Vfunc_get__45__Vfuncout = 0;
    uvmt_fifo_tb_uvma_rd_if* __Vfunc_get__45__value;
    __Vfunc_get__45__value = nullptr;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__46__Vfuncout;
    __Vfunc_uvm_report_enabled__46__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__48__Vfuncout;
    __Vfunc_uvm_report_enabled__48__Vfuncout = 0;
    // Body
    if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 170)
        ->__PVT__enabled) {
        if ((1U & (~ ([&]() {
                            __Vfunc_get__42__value 
                                = VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 171)
                                ->__PVT__wr_vif;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz2__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, ""s, "wr_vif"s, __Vfunc_get__42__value, __Vfunc_get__42__Vfuncout);
                            VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 171)
                      ->__PVT__wr_vif = __Vfunc_get__42__value;
                        }(), (IData)(__Vfunc_get__42__Vfuncout))))) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "wr_vif"s, __Vfunc_uvm_report_enabled__43__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__43__Vfuncout))) {
                this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "wr_vif"s, "virtual interface must be set for wr_vif!"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x000000acU, ""s, 1U);
            }
        }
        if ((1U & (~ ([&]() {
                            __Vfunc_get__45__value 
                                = VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 175)
                                ->__PVT__rd_vif;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz3__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, ""s, "rd_vif"s, __Vfunc_get__45__value, __Vfunc_get__45__Vfuncout);
                            VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 175)
                      ->__PVT__rd_vif = __Vfunc_get__45__value;
                        }(), (IData)(__Vfunc_get__45__Vfuncout))))) {
            if ((0U != ([&]() {
                            this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "rd_vif"s, __Vfunc_uvm_report_enabled__46__Vfuncout);
                        }(), __Vfunc_uvm_report_enabled__46__Vfuncout))) {
                this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "rd_vif"s, "virtual interface must be set for rd_vif!"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x000000b0U, ""s, 1U);
            }
        }
    } else if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "ENV"s, __Vfunc_uvm_report_enabled__48__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__48__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "ENV"s, "cfg is null, skip retrieving vifs."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh"s, 0x000000b4U, ""s, 1U);
    }
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_assign_cfg(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_assign_cfg\n"); );
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz146__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, "*"s, "cfg"s, this->__PVT__cfg);
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz158__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, "*write_agent"s, "cfg"s, VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 190)
                                                                                ->__PVT__write_cfg);
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz158__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, "*read_agent"s, "cfg"s, VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 191)
                                                                                ->__PVT__read_cfg);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_assign_cntxt(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_assign_cntxt\n"); );
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz147__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, "*"s, "cntxt"s, this->__PVT__cntxt);
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz159__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, "*write_agent"s, "cntxt"s, VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 199)
                                                                                ->__PVT__write_cntxt);
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz159__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, "*read_agent"s, "cntxt"s, VL_NULL_CHECK(this->__PVT__cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 200)
                                                                                ->__PVT__read_cntxt);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_create_agents(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_create_agents\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154> __Vfunc_create__56__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155> __Vfunc_create__57__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi87__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "write_agent"s, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, ""s, __Vfunc_create__56__Vfuncout);
    this->__PVT__write_agent = __Vfunc_create__56__Vfuncout;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi89__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "read_agent"s, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, ""s, __Vfunc_create__57__Vfuncout);
    this->__PVT__read_agent = __Vfunc_create__57__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_create_env_components(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_create_env_components\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c> __Vfunc_create__58__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c> __Vfunc_create__59__Vfuncout;
    // Body
    if (VL_NULL_CHECK(this->__PVT__cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 220)
        ->__PVT__scoreboard_enabled) {
        vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi76__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "predictor"s, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, ""s, __Vfunc_create__58__Vfuncout);
        this->__PVT__predictor = __Vfunc_create__58__Vfuncout;
        vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi81__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "scoreboard"s, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, ""s, __Vfunc_create__59__Vfuncout);
        this->__PVT__scoreboard = __Vfunc_create__59__Vfuncout;
    }
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_create_vsequencer(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_create_vsequencer\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_vsqr_c> __Vfunc_create__60__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi73__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "vsequencer"s, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>{this}, ""s, __Vfunc_create__60__Vfuncout);
    this->__PVT__vsequencer = __Vfunc_create__60__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_create_cov_model(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_create_cov_model\n"); );
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_connect_predictor(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_connect_predictor\n"); );
    // Body
    VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__write_agent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 244)
                  ->__PVT__drv_ap, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 244)->__VnoInFunc_connect(vlProcess, vlSymsp, VL_NULL_CHECK(this->__PVT__predictor, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 244)
                                                                                ->__PVT__wr_input_imp);
    VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__read_agent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 245)
                  ->__PVT__drv_ap, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 245)->__VnoInFunc_connect(vlProcess, vlSymsp, VL_NULL_CHECK(this->__PVT__predictor, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 245)
                                                                                ->__PVT__rd_input_imp);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_connect_scoreboard(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_connect_scoreboard\n"); );
    // Body
    VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__write_agent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 252)
                  ->__PVT__mon_ap, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 252)->__VnoInFunc_connect(vlProcess, vlSymsp, VL_NULL_CHECK(this->__PVT__scoreboard, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 252)
                                                                                ->__PVT__wr_act_imp);
    VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__read_agent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 253)
                  ->__PVT__mon_ap, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 253)->__VnoInFunc_connect(vlProcess, vlSymsp, VL_NULL_CHECK(this->__PVT__scoreboard, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 253)
                                                                                ->__PVT__rd_act_imp);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_connect_cov_model(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_connect_cov_model\n"); );
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_assemble_vsequencer(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_assemble_vsequencer\n"); );
    // Body
    VL_NULL_CHECK(this->__PVT__vsequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 267)->__PVT__write_sqr 
        = VL_NULL_CHECK(this->__PVT__write_agent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 267)
        ->__PVT__sqr;
    VL_NULL_CHECK(this->__PVT__vsequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 268)->__PVT__read_sqr 
        = VL_NULL_CHECK(this->__PVT__read_agent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_env.svh", 268)
        ->__PVT__sqr;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__66__Vfuncout;
    __Vfunc___VBasicRand__66__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__66__Vfuncout);
            }(), __Vfunc___VBasicRand__66__Vfuncout));
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += "cfg:" + VL_TO_STRING(__PVT__cfg);
    out += ", cntxt:" + VL_TO_STRING(__PVT__cntxt);
    out += ", predictor:" + VL_TO_STRING(__PVT__predictor);
    out += ", scoreboard:" + VL_TO_STRING(__PVT__scoreboard);
    out += ", vsequencer:" + VL_TO_STRING(__PVT__vsequencer);
    out += ", write_agent:" + VL_TO_STRING(__PVT__write_agent);
    out += ", read_agent:" + VL_TO_STRING(__PVT__read_agent);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_env::to_string_middle();
    return (out);
}
