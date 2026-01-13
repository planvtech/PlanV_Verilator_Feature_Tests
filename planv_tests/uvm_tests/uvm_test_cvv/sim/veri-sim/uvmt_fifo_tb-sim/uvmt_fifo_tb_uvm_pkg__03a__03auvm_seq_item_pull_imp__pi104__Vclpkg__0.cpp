// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_> imp)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz208(vlProcess, vlSymsp, name, imp, 2U, 1U, 1U) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    this->__PVT__m_imp = imp;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz208::__PVT__m_if_mask = 0x000001ffU;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_seq_item_pull_imp"s;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_disable_auto_item_recording(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_disable_auto_item_recording\n"); );
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_disable_auto_item_recording(vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_is_auto_item_recording_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_auto_item_recording_enabled__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_is_auto_item_recording_enabled\n"); );
    // Locals
    CData/*0:0*/ __Vtask_is_auto_item_recording_enabled__2__Vfuncout;
    __Vtask_is_auto_item_recording_enabled__2__Vfuncout = 0;
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_is_auto_item_recording_enabled(vlSymsp, __Vtask_is_auto_item_recording_enabled__2__Vfuncout);
    is_auto_item_recording_enabled__Vfuncrtn = __Vtask_is_auto_item_recording_enabled__2__Vfuncout;
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_get_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_get_next_item\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_get_next_item__3__t;
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_get_next_item(vlSymsp, __Vtask_get_next_item__3__t);
    t = __Vtask_get_next_item__3__t;
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_try_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_try_next_item\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_try_next_item__4__t;
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_try_next_item(vlSymsp, __Vtask_try_next_item__4__t);
    t = __Vtask_try_next_item__4__t;
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_item_done(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_item_done\n"); );
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_item_done(vlSymsp, t);
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_wait_for_sequences(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_wait_for_sequences\n"); );
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_wait_for_sequences(vlProcess, vlSymsp);
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_has_do_available(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &has_do_available__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_has_do_available\n"); );
    // Locals
    CData/*0:0*/ __Vtask_has_do_available__7__Vfuncout;
    __Vtask_has_do_available__7__Vfuncout = 0;
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_has_do_available(vlSymsp, __Vtask_has_do_available__7__Vfuncout);
    has_do_available__Vfuncrtn = __Vtask_has_do_available__7__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_put_response(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_put_response\n"); );
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_put_response(vlProcess, vlSymsp, t);
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_get\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_get__9__t;
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_get(vlSymsp, __Vtask_get__9__t);
    t = __Vtask_get__9__t;
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_peek\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_peek__10__t;
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_peek(vlSymsp, __Vtask_peek__10__t);
    t = __Vtask_peek__10__t;
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::__VnoInFunc_put\n"); );
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 87)->__VnoInFunc_put(vlSymsp, t);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104::to_string_middle\n"); );
    // Body
    std::string out;
    out += "m_imp:" + VL_TO_STRING(__PVT__m_imp);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz208::to_string_middle();
    return (out);
}
