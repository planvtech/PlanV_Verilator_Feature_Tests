// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi68> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi68> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi68__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvmt_fifo_base_test_c"s;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi68> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi68__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvmt_fifo_base_test_c"s;
}

uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_test(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_build_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__3__Vfuncout;
    __Vfunc_uvm_report_enabled__3__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__8__Vfuncout;
    __Vfunc_uvm_report_enabled__8__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__14__Vfuncout;
    __Vfunc_uvm_report_enabled__14__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_build_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__3__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__3__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Entered build_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x00000055U, ""s, 1U);
    }
    this->__VnoInFunc_retrieve_vifs(vlProcess, vlSymsp);
    this->__VnoInFunc_create_cfg_and_cntxt(vlProcess, vlSymsp);
    this->__VnoInFunc_randomize_test(vlProcess, vlSymsp);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x00000064U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__8__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__8__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, VL_SFORMATF_N_NX("##### After randomize: env_cfg.enabled=%0#",0,
                                                                                1,
                                                                                VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 90)
                                                                                ->__PVT__enabled) , 0x00000064U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x0000005aU, ""s, 1U);
    }
    this->__VnoInFunc_assign_cfg(vlProcess, vlSymsp);
    this->__VnoInFunc_assign_cntxt(vlProcess, vlSymsp);
    this->__VnoInFunc_create_env(vlProcess, vlSymsp);
    this->__VnoInFunc_create_components(vlSymsp);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__14__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__14__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Exiting build_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x00000061U, ""s, 1U);
    }
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_connect_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_connect_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__17__Vfuncout;
    __Vfunc_uvm_report_enabled__17__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__19__Vfuncout;
    __Vfunc_uvm_report_enabled__19__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_connect_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__17__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__17__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Entered connect_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x0000006aU, ""s, 1U);
    }
    this->__PVT__vsqr = VL_NULL_CHECK(this->__PVT__env, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 108)
        ->__PVT__vsequencer;
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__19__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__19__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Exiting connect_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x0000006eU, ""s, 1U);
    }
}

VlCoroutine uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_run_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_run_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__22__Vfuncout;
    __Vfunc_uvm_report_enabled__22__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__25__Vfuncout;
    __Vfunc_uvm_report_enabled__25__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__27__Vfuncout;
    __Vfunc_uvm_report_enabled__27__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__29__Vfuncout;
    __Vfunc_uvm_report_enabled__29__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__33__Vfuncout;
    __Vfunc_uvm_report_enabled__33__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__35__Vfuncout;
    __Vfunc_uvm_report_enabled__35__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    VL_NULL_CHECK(phase, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 120)->__VnoInFunc_raise_objection(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c>{this}, "Test is running"s, 1U);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x00000064U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__22__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__22__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Raised objection BEFORE super.run_phase()"s, 0x00000064U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x00000079U, ""s, 1U);
    }
    co_await uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_run_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__25__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__25__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Entered run_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x0000007dU, ""s, 1U);
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x00000064U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__27__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__27__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "About to wait 2000ns"s, 0x00000064U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x00000080U, ""s, 1U);
    }
    co_await vlSymsp->TOP.__VdlySched.delay(0x00000000001e8480ULL, 
                                            vlProcess, 
                                            "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 
                                            129);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x00000064U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__29__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__29__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Finished waiting 2000ns"s, 0x00000064U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x00000082U, ""s, 1U);
    }
    this->__VnoInFunc_watchdog_timer(vlProcess, vlSymsp);
    VL_NULL_CHECK(phase, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 135)->__VnoInFunc_drop_objection(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c>{this}, "Test completed"s, 1U);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x00000064U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__33__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__33__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Dropped objection"s, 0x00000064U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x00000088U, ""s, 1U);
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__35__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__35__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Exiting run_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x0000008aU, ""s, 1U);
    }
    co_return;}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_report_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_report_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__38__Vfuncout;
    __Vfunc_uvm_report_enabled__38__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_component::__VnoInFunc_report_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "TEST"s, __Vfunc_uvm_report_enabled__38__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__38__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "TEST"s, "Entered report_phase, set sim_finished high to notify the testbench."s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x00000092U, ""s, 1U);
    }
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz4__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, VlNull{}, ""s, "sim_finished"s, 1U);
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_retrieve_vifs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_retrieve_vifs\n"); );
    // Locals
    CData/*0:0*/ __Vfunc_get__41__Vfuncout;
    __Vfunc_get__41__Vfuncout = 0;
    uvmt_fifo_tb_uvmt_fifo_clk_gen_if* __Vfunc_get__41__value;
    __Vfunc_get__41__value = nullptr;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__42__Vfuncout;
    __Vfunc_uvm_report_enabled__42__Vfuncout = 0;
    CData/*0:0*/ __Vfunc_get__44__Vfuncout;
    __Vfunc_get__44__Vfuncout = 0;
    uvmt_fifo_tb_uvmt_fifo_clk_gen_if* __Vfunc_get__44__value;
    __Vfunc_get__44__value = nullptr;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__45__Vfuncout;
    __Vfunc_uvm_report_enabled__45__Vfuncout = 0;
    // Body
    if ((1U & (~ ([&]() {
                        __Vfunc_get__41__value = this->__PVT__wr_clk_gen_vif;
                        vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz1__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c>{this}, ""s, "wr_clk_gen_vif"s, __Vfunc_get__41__value, __Vfunc_get__41__Vfuncout);
                        this->__PVT__wr_clk_gen_vif 
                            = __Vfunc_get__41__value;
                    }(), (IData)(__Vfunc_get__41__Vfuncout))))) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "VIF"s, __Vfunc_uvm_report_enabled__42__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__42__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "VIF"s, "wr_clk_gen_vif is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x0000009bU, ""s, 1U);
        }
    }
    if ((1U & (~ ([&]() {
                        __Vfunc_get__44__value = this->__PVT__rd_clk_gen_vif;
                        vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz1__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c>{this}, ""s, "rd_clk_gen_vif"s, __Vfunc_get__44__value, __Vfunc_get__44__Vfuncout);
                        this->__PVT__rd_clk_gen_vif 
                            = __Vfunc_get__44__value;
                    }(), (IData)(__Vfunc_get__44__Vfuncout))))) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "VIF"s, __Vfunc_uvm_report_enabled__45__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__45__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "VIF"s, "rd_clk_gen_vif is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x0000009fU, ""s, 1U);
        }
    }
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_create_cfg_and_cntxt(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_create_cfg_and_cntxt\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_cfg_c> __Vfunc_create__47__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c> __Vfunc_create__48__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c> __Vfunc_create__49__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c> __Vfunc_create__50__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi66__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "test_cfg"s, VlNull{}, ""s, __Vfunc_create__47__Vfuncout);
    this->__PVT__test_cfg = __Vfunc_create__47__Vfuncout;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi70__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "env_cfg"s, VlNull{}, ""s, __Vfunc_create__48__Vfuncout);
    this->__PVT__env_cfg = __Vfunc_create__48__Vfuncout;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi67__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "test_randvars"s, VlNull{}, ""s, __Vfunc_create__49__Vfuncout);
    this->__PVT__test_randvars = __Vfunc_create__49__Vfuncout;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi71__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "env_cntxt"s, VlNull{}, ""s, __Vfunc_create__50__Vfuncout);
    this->__PVT__env_cntxt = __Vfunc_create__50__Vfuncout;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_randomize_test(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_randomize_test\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VStdrand_h80dc4f1c__0__51__Vfuncout;
    __Vfunc___VStdrand_h80dc4f1c__0__51__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__52__Vfuncout;
    __Vfunc_uvm_report_enabled__52__Vfuncout = 0;
    // Body
    if ((1U & (~ (0U != ([&]() {
                            this->__VnoInFunc___VStdrand_h80dc4f1c__0(vlSymsp, __Vfunc___VStdrand_h80dc4f1c__0__51__Vfuncout);
                        }(), __Vfunc___VStdrand_h80dc4f1c__0__51__Vfuncout))))) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "RANDOMIZE"s, __Vfunc_uvm_report_enabled__52__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__52__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "RANDOMIZE"s, "Randomization failed"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x000000b3U, ""s, 1U);
        }
    }
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_assign_cfg(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_assign_cfg\n"); );
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz146__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c>{this}, "env"s, "cfg"s, this->__PVT__env_cfg);
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_assign_cntxt(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_assign_cntxt\n"); );
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz147__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c>{this}, "env"s, "cntxt"s, this->__PVT__env_cntxt);
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_create_env(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_create_env\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c> __Vfunc_create__56__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi72__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "env"s, 
                                                                                VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c>{this}, ""s, __Vfunc_create__56__Vfuncout);
    this->__PVT__env = __Vfunc_create__56__Vfuncout;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_create_components(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_create_components\n"); );
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_watchdog_timer(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_watchdog_timer\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vfunc_self__57__Vfuncout;
    // Body
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk1__DOT____VforkParent;
    vlSymsp->TOP__std__03a__03aprocess__Vclpkg.__VnoInFunc_self(vlProcess, vlSymsp, __Vfunc_self__57__Vfuncout);
    unnamedblk1__DOT____VforkParent = __Vfunc_self__57__Vfuncout;
    this->__VnoInFunc_watchdog_timer____Vfork_1__0(std::make_shared<VlProcess>(vlProcess), vlSymsp, unnamedblk1__DOT____VforkParent);
}

VlCoroutine uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_watchdog_timer____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk1__DOT____VforkParent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_watchdog_timer____Vfork_1__0\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vtask___VforkTask_0__58____VforkParent;
    IData/*31:0*/ __Vtask_status__59__Vfuncout;
    __Vtask_status__59__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__60__Vfuncout;
    __Vfunc_uvm_report_enabled__60__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    __Vtask___VforkTask_0__58____VforkParent = unnamedblk1__DOT____VforkParent;
    if ((1U == ([&]() {
                    VL_NULL_CHECK(__Vtask___VforkTask_0__58____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 215)
                ->__VnoInFunc_status(vlSymsp, __Vtask_status__59__Vfuncout);
                }(), __Vtask_status__59__Vfuncout))) {
        CData/*0:0*/ __VdynTrigger_h4efc5f02__0;
        __VdynTrigger_h4efc5f02__0 = 0;
        __VdynTrigger_h4efc5f02__0 = 0U;
        while ((1U & (~ (IData)(__VdynTrigger_h4efc5f02__0)))) {
            co_await vlSymsp->TOP.__VdynSched.evaluation(
                                                         vlProcess, 
                                                         "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvmt_fifo_pkg::uvmt_fifo_base_test_c.__Vtask___VforkTask_0__58____VforkParent.(uvmt_fifo_pkg::uvmt_fifo_base_test_c.__Vtask_status__59__Vfuncout); , ); ))", 
                                                         "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 
                                                         215);
            this->__Vtrigprevexpr_h34f2bc4d__0 = (1U 
                                                  != 
                                                  ([&]() {
                        VL_NULL_CHECK(__Vtask___VforkTask_0__58____VforkParent, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 215)
                                                   ->__VnoInFunc_status(vlSymsp, __Vtask_status__59__Vfuncout);
                    }(), __Vtask_status__59__Vfuncout));
            __VdynTrigger_h4efc5f02__0 = this->__Vtrigprevexpr_h34f2bc4d__0;
            vlSymsp->TOP.__VdynSched.anyTriggered(__VdynTrigger_h4efc5f02__0);
        }
        co_await vlSymsp->TOP.__VdynSched.resumption(
                                                     vlProcess, 
                                                     "@([true] (32'h1 != $_EXPRSTMT( // Function: status uvmt_fifo_pkg::uvmt_fifo_base_test_c.__Vtask___VforkTask_0__58____VforkParent.(uvmt_fifo_pkg::uvmt_fifo_base_test_c.__Vtask_status__59__Vfuncout); , ); ))", 
                                                     "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 
                                                     215);
    }
    co_await vlSymsp->TOP.__VdlySched.delay(0x00000000000003e8ULL, 
                                            vlProcess, 
                                            "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 
                                            217);
    VL_WRITEF_NX("\n%Nuvmt_fifo_pkg.uvmt_fifo_base_test_c.__VforkTask_0: Watchdog timer will wait for %0dns\n\n",0,
                 vlSymsp->name(),64,VL_RTOIROUND_Q_D(
                                                     (1.0 
                                                      * 
                                                      VL_ITOR_D_I(32, VL_NULL_CHECK(this->__PVT__test_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 218)
                                                                  ->__PVT__watchdog_timeout))));
    co_await vlSymsp->TOP.__VdlySched.delay(VL_RTOIROUND_Q_D(
                                                             (1.00000000000000000e+03 
                                                              * 
                                                              VL_ITOR_D_I(32, VL_NULL_CHECK(this->__PVT__test_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 219)
                                                                          ->__PVT__watchdog_timeout))), 
                                            vlProcess, 
                                            "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 
                                            219);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "TIMEOUT"s, __Vfunc_uvm_report_enabled__60__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__60__Vfuncout))) {
        this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "TIMEOUT"s, "Test timed out"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh"s, 0x000000dcU, ""s, 1U);
    }
    vlProcess->state(VlProcess::FINISHED);
    co_return;}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__63__Vfuncout;
    __Vfunc___VBasicRand__63__Vfuncout = 0;
    // Body
    std::cout << "[DEBUG] __VnoInFunc_randomize called (REAL randomize with constraints)" << std::endl;
    std::cout << "[DEBUG] env_cfg.enabled BEFORE write_var = " << (int)VL_NULL_CHECK(this->__PVT__env_cfg, "debug", 1)->__PVT__enabled << std::endl;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 46)
                                                                        ->__PVT__enabled, 1ULL, 
                                                                        "env_cfg.enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 47)
                                                                        ->__PVT__is_active, 1ULL, 
                                                                        "env_cfg.is_active", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 48)
                                                                        ->__PVT__scoreboard_enabled, 1ULL, 
                                                                        "env_cfg.scoreboard_enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 49)
                                                                        ->__PVT__cov_model_enabled, 1ULL, 
                                                                        "env_cfg.cov_model_enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__test_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                        ->__PVT__watchdog_timeout, 0x0000000000000020ULL, 
                                                                        "test_cfg.watchdog_timeout", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 48)
                                                                        ->__PVT__enabled, 1ULL, 
                                                                        "env_cfg.write_cfg.enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 49)
                                                                        ->__PVT__enabled, 1ULL, 
                                                                        "env_cfg.read_cfg.enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 53)
                                                                        ->__PVT__is_active, 1ULL, 
                                                                        "env_cfg.write_cfg.is_active", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 54)
                                                                        ->__PVT__is_active, 1ULL, 
                                                                        "env_cfg.read_cfg.is_active", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 57)
                                                                        ->__PVT__wr_or_rd, 1ULL, 
                                                                        "env_cfg.write_cfg.wr_or_rd", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 58)
                                                                        ->__PVT__wr_or_rd, 1ULL, 
                                                                        "env_cfg.read_cfg.wr_or_rd", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    std::cout << "[DEBUG] Before constraint.next(), env_cfg.enabled = " << (int)VL_NULL_CHECK(this->__PVT__env_cfg, "debug", 1)->__PVT__enabled << std::endl;
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    std::cout << "[DEBUG] After constraint.next(), solver returned: " << randomize__Vfuncrtn << std::endl;
    std::cout << "[DEBUG] After constraint.next(), env_cfg.enabled = " << (int)VL_NULL_CHECK(this->__PVT__env_cfg, "debug", 1)->__PVT__enabled << std::endl;
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__63__Vfuncout);
            }(), __Vfunc___VBasicRand__63__Vfuncout));
    std::cout << "[DEBUG] After __VBasicRand(), final result: " << randomize__Vfuncrtn << std::endl;
    std::cout << "[DEBUG] After __VBasicRand(), env_cfg.enabled = " << (int)VL_NULL_CHECK(this->__PVT__env_cfg, "debug", 1)->__PVT__enabled << std::endl;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc___VStdrand_h80dc4f1c__0(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VStdrand_h80dc4f1c__0__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc___VStdrand_h80dc4f1c__0\n"); );
    // Body
    std::cout << "[DEBUG] __VStdrand_h80dc4f1c__0 called - REDIRECTING to real randomize()" << std::endl;
    // FIX: Call the real randomize() function instead of returning stub value
    this->__VnoInFunc_randomize(vlSymsp, __VStdrand_h80dc4f1c__0__Vfuncrtn);
    std::cout << "[DEBUG] After real randomize(), result = " << __VStdrand_h80dc4f1c__0__Vfuncrtn << std::endl;
    std::cout << "[DEBUG] env_cfg.enabled = " << (int)VL_NULL_CHECK(this->__PVT__env_cfg, "debug", 1)->__PVT__enabled << std::endl;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_env_cfg_con_setup_constraint(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_env_cfg_con_setup_constraint\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (= ((_ zero_extend 31) env_cfg.enabled) #x00000001))"s);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (= env_cfg.is_active #b1))"s);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (= ((_ zero_extend 31) env_cfg.scoreboard_enabled) #x00000001))"s);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (= ((_ zero_extend 31) env_cfg.cov_model_enabled) #x00000000))"s);
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc___Vsetup_constraints\n"); );
    // Body
    this->__VnoInFunc_env_cfg_con_setup_constraint(vlSymsp);
    this->__VnoInFunc_test_cfg__DT__timeout_default_cons_setup_constraint(vlSymsp);
    this->__VnoInFunc_env_cfg__DT__agent_cfg_cons_setup_constraint(vlSymsp);
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_test_cfg__DT__timeout_default_cons_setup_constraint(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_test_cfg__DT__timeout_default_cons_setup_constraint\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (= test_cfg.watchdog_timeout #x05f5e100))"s);
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_env_cfg__DT__agent_cfg_cons_setup_constraint(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc_env_cfg__DT__agent_cfg_cons_setup_constraint\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (=> (__Vbool env_cfg.enabled) (__Vbool (bvand (__Vbv (= ((_ zero_extend 31) env_cfg.write_cfg.enabled) #x00000001)) (__Vbv (= ((_ zero_extend 31) env_cfg.read_cfg.enabled) #x00000001))))))"s);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (=> (__Vbool (__Vbv (= env_cfg.is_active #b1))) (__Vbool (bvand (__Vbv (= env_cfg.write_cfg.is_active #b1)) (__Vbv (= env_cfg.read_cfg.is_active #b1))))))"s);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (= env_cfg.write_cfg.wr_or_rd #b0))"s);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (= env_cfg.read_cfg.wr_or_rd #b1))"s);
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__VnoInFunc___VBasicRand\n"); );
    // Locals
    IData/*31:0*/ __Vtask___VBasicRand__67__Vfuncout;
    __Vtask___VBasicRand__67__Vfuncout = 0;
    IData/*31:0*/ __Vtask___VBasicRand__68__Vfuncout;
    __Vtask___VBasicRand__68__Vfuncout = 0;
    IData/*31:0*/ __Vtask___VBasicRand__69__Vfuncout;
    __Vtask___VBasicRand__69__Vfuncout = 0;
    IData/*31:0*/ __Vtask___VBasicRand__70__Vfuncout;
    __Vtask___VBasicRand__70__Vfuncout = 0;
    // Body
    __VBasicRand__Vfuncrtn = 1U;
    if ((VlNull{} != this->__PVT__test_cfg)) {
        __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                  & ([&]() {
                    VL_NULL_CHECK(this->__PVT__test_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 12)
                                     ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__67__Vfuncout);
                }(), __Vtask___VBasicRand__67__Vfuncout));
    }
    if ((VlNull{} != this->__PVT__test_randvars)) {
        __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                  & ([&]() {
                    VL_NULL_CHECK(this->__PVT__test_randvars, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 12)
                                     ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__68__Vfuncout);
                }(), __Vtask___VBasicRand__68__Vfuncout));
    }
    if ((VlNull{} != this->__PVT__env_cfg)) {
        __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                  & ([&]() {
                    VL_NULL_CHECK(this->__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 12)
                                     ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__69__Vfuncout);
                }(), __Vtask___VBasicRand__69__Vfuncout));
    }
    if ((VlNull{} != this->__PVT__env_cntxt)) {
        __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                  & ([&]() {
                    VL_NULL_CHECK(this->__PVT__env_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 12)
                                     ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__70__Vfuncout);
                }(), __Vtask___VBasicRand__70__Vfuncout));
    }
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__rd_clk_gen_vif = nullptr;
    __PVT__wr_clk_gen_vif = nullptr;
    __PVT__success = 0;
    __Vtrigprevexpr_h34f2bc4d__0 = 0;
}

uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::~uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                          uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += "test_cfg:" + VL_TO_STRING(__PVT__test_cfg);
    out += ", test_randvars:" + VL_TO_STRING(__PVT__test_randvars);
    out += ", env_cfg:" + VL_TO_STRING(__PVT__env_cfg);
    out += ", env_cntxt:" + VL_TO_STRING(__PVT__env_cntxt);
    out += ", env:" + VL_TO_STRING(__PVT__env);
    out += ", vsqr:" + VL_TO_STRING(__PVT__vsqr);
    out += ", rd_clk_gen_vif:" + VL_TO_STRING(__PVT__rd_clk_gen_vif);
    out += ", wr_clk_gen_vif:" + VL_TO_STRING(__PVT__wr_clk_gen_vif);
    out += ", success:" + VL_TO_STRING(__PVT__success);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_test::to_string_middle();
    return (out);
}
