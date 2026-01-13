// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi69> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi69> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi69__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvmt_fifo_test_case1_c"s;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi69> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi69__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvmt_fifo_test_case1_c"s;
}

uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__3__Vfuncout;
    __Vfunc___VBasicRand__3__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 46)
                                                                        ->__PVT__enabled, 1ULL, 
                                                                        "env_cfg.enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 47)
                                                                        ->__PVT__is_active, 1ULL, 
                                                                        "env_cfg.is_active", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 48)
                                                                        ->__PVT__scoreboard_enabled, 1ULL, 
                                                                        "env_cfg.scoreboard_enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 49)
                                                                        ->__PVT__cov_model_enabled, 1ULL, 
                                                                        "env_cfg.cov_model_enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__test_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                        ->__PVT__watchdog_timeout, 0x0000000000000020ULL, 
                                                                        "test_cfg.watchdog_timeout", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 48)
                                                                        ->__PVT__enabled, 1ULL, 
                                                                        "env_cfg.write_cfg.enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 49)
                                                                        ->__PVT__enabled, 1ULL, 
                                                                        "env_cfg.read_cfg.enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 53)
                                                                        ->__PVT__is_active, 1ULL, 
                                                                        "env_cfg.write_cfg.is_active", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 54)
                                                                        ->__PVT__is_active, 1ULL, 
                                                                        "env_cfg.read_cfg.is_active", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 57)
                                                                        ->__PVT__wr_or_rd, 1ULL, 
                                                                        "env_cfg.write_cfg.wr_or_rd", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/base_test/uvmt_fifo_base_test.svh", 178)
                                                                                ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 58)
                                                                        ->__PVT__wr_or_rd, 1ULL, 
                                                                        "env_cfg.read_cfg.wr_or_rd", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__3__Vfuncout);
            }(), __Vfunc___VBasicRand__3__Vfuncout));
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc___Vsetup_constraints\n"); );
    // Body
    this->__VnoInFunc_env_cfg_con_setup_constraint(vlSymsp);
    this->__VnoInFunc_test_cfg__DT__timeout_default_cons_setup_constraint(vlSymsp);
    this->__VnoInFunc_env_cfg__DT__agent_cfg_cons_setup_constraint(vlSymsp);
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::__VnoInFunc___VBasicRand\n"); );
    // Locals
    IData/*31:0*/ __Vtask___VBasicRand__7__Vfuncout;
    __Vtask___VBasicRand__7__Vfuncout = 0;
    IData/*31:0*/ __Vtask___VBasicRand__8__Vfuncout;
    __Vtask___VBasicRand__8__Vfuncout = 0;
    IData/*31:0*/ __Vtask___VBasicRand__9__Vfuncout;
    __Vtask___VBasicRand__9__Vfuncout = 0;
    IData/*31:0*/ __Vtask___VBasicRand__10__Vfuncout;
    __Vtask___VBasicRand__10__Vfuncout = 0;
    // Body
    __VBasicRand__Vfuncrtn = 1U;
    if ((VlNull{} != uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__test_cfg)) {
        __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                  & ([&]() {
                    VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__test_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/uvmt_fifo_test_case1.svh", 12)
                                     ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__7__Vfuncout);
                }(), __Vtask___VBasicRand__7__Vfuncout));
    }
    if ((VlNull{} != uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__test_randvars)) {
        __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                  & ([&]() {
                    VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__test_randvars, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/uvmt_fifo_test_case1.svh", 12)
                                     ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__8__Vfuncout);
                }(), __Vtask___VBasicRand__8__Vfuncout));
    }
    if ((VlNull{} != uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg)) {
        __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                  & ([&]() {
                    VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/uvmt_fifo_test_case1.svh", 12)
                                     ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__9__Vfuncout);
                }(), __Vtask___VBasicRand__9__Vfuncout));
    }
    if ((VlNull{} != uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cntxt)) {
        __VBasicRand__Vfuncrtn = (__VBasicRand__Vfuncrtn 
                                  & ([&]() {
                    VL_NULL_CHECK(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::__PVT__env_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tests/uvmt_fifo_test_case1.svh", 12)
                                     ->__VnoInFunc___VBasicRand(vlSymsp, __Vtask___VBasicRand__10__Vfuncout);
                }(), __Vtask___VBasicRand__10__Vfuncout));
    }
}

void uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::~uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_case1_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c::to_string_middle();
    return (out);
}
