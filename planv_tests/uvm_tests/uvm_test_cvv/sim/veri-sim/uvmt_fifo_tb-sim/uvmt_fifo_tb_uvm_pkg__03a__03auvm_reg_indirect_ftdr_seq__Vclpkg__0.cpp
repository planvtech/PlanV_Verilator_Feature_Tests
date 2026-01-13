// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> addr_reg, IData/*31:0*/ idx, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> data_reg)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor(vlProcess, vlSymsp, "uvm_reg_indirect_ftdr_seq"s) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    this->__PVT__m_addr_reg = addr_reg;
    this->__PVT__m_idx = idx;
    this->__PVT__m_data_reg = data_reg;
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::__VnoInFunc_body(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::__VnoInFunc_body\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_clone__1__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_clone__5__Vfuncout;
    // Body
    VL_KEEP_THIS;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw;
    {
        if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor::__PVT__rw_info, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 287)
                                             ->__VnoInFunc_clone(vlProcess, vlSymsp, __Vtask_clone__1__Vfuncout);
                                }(), __Vtask_clone__1__Vfuncout), rw))))) {
            VL_WRITEF_NX("[%0t] %%Error: uvm_reg_indirect.svh:287: Assertion failed in %Nuvm_pkg.uvm_reg_indirect_ftdr_seq.body: '$cast' failed.\n",0,
                         64,VL_TIME_UNITED_Q(1000),
                         -9,vlSymsp->name());
            VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 287, "");
        }
        VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 288)->__PVT__element 
            = this->__PVT__m_addr_reg;
        VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 289)->__PVT__kind = 1U;
        VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 290)->__PVT__value.atWrite(0U) 
            = VL_EXTENDS_QI(64,32, this->__PVT__m_idx);
        co_await VL_NULL_CHECK(this->__PVT__m_addr_reg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 292)->__VnoInFunc_XatomicX(vlProcess, vlSymsp, 1U);
        co_await VL_NULL_CHECK(this->__PVT__m_data_reg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 293)->__VnoInFunc_XatomicX(vlProcess, vlSymsp, 1U);
        co_await VL_NULL_CHECK(this->__PVT__m_addr_reg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 295)->__VnoInFunc_do_write(vlProcess, vlSymsp, rw);
        if ((1U == VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 297)
             ->__PVT__status)) {
            goto __Vlabel0;
        }
        if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor::__PVT__rw_info, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 300)
                                             ->__VnoInFunc_clone(vlProcess, vlSymsp, __Vtask_clone__5__Vfuncout);
                                }(), __Vtask_clone__5__Vfuncout), rw))))) {
            VL_WRITEF_NX("[%0t] %%Error: uvm_reg_indirect.svh:300: Assertion failed in %Nuvm_pkg.uvm_reg_indirect_ftdr_seq.body: '$cast' failed.\n",0,
                         64,VL_TIME_UNITED_Q(1000),
                         -9,vlSymsp->name());
            VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 300, "");
        }
        VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 301)->__PVT__element 
            = this->__PVT__m_data_reg;
        if ((1U == VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor::__PVT__rw_info, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 303)
             ->__PVT__kind)) {
            co_await VL_NULL_CHECK(this->__PVT__m_data_reg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 304)->__VnoInFunc_do_write(vlProcess, vlSymsp, rw);
        } else {
            co_await VL_NULL_CHECK(this->__PVT__m_data_reg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 306)->__VnoInFunc_do_read(vlProcess, vlSymsp, rw);
            VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor::__PVT__rw_info, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 307)->__PVT__value.atWrite(0U) 
                = VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 307)
                ->__PVT__value.at(0U);
        }
        co_await VL_NULL_CHECK(this->__PVT__m_addr_reg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 310)->__VnoInFunc_XatomicX(vlProcess, vlSymsp, 0U);
        co_await VL_NULL_CHECK(this->__PVT__m_data_reg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 311)->__VnoInFunc_XatomicX(vlProcess, vlSymsp, 0U);
        VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor::__PVT__rw_info, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 313)->__PVT__status 
            = VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_indirect.svh", 313)
            ->__PVT__status;
        __Vlabel0: ;
    }
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__11__Vfuncout;
    __Vfunc___VBasicRand__11__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__11__Vfuncout);
            }(), __Vfunc___VBasicRand__11__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__m_idx = 0;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq::to_string_middle\n"); );
    // Body
    std::string out;
    out += "m_addr_reg:" + VL_TO_STRING(__PVT__m_addr_reg);
    out += ", m_data_reg:" + VL_TO_STRING(__PVT__m_data_reg);
    out += ", m_idx:" + VL_TO_STRING(__PVT__m_idx);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor::to_string_middle();
    return (out);
}
