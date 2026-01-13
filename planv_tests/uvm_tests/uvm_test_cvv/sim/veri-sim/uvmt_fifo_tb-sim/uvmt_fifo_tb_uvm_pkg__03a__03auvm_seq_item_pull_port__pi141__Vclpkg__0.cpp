// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent, IData/*31:0*/ min_size, IData/*31:0*/ max_size)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232(vlProcess, vlSymsp, name, parent, 0U, min_size, max_size) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if_mask = 0x000001ffU;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_seq_item_pull_port"s;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_disable_auto_item_recording(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_disable_auto_item_recording\n"); );
    // Body
    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_disable_auto_item_recording(vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_is_auto_item_recording_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_auto_item_recording_enabled__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_is_auto_item_recording_enabled\n"); );
    // Locals
    CData/*0:0*/ __Vtask_is_auto_item_recording_enabled__2__Vfuncout;
    __Vtask_is_auto_item_recording_enabled__2__Vfuncout = 0;
    // Body
    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_is_auto_item_recording_enabled(vlSymsp, __Vtask_is_auto_item_recording_enabled__2__Vfuncout);
    is_auto_item_recording_enabled__Vfuncrtn = __Vtask_is_auto_item_recording_enabled__2__Vfuncout;
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_get_next_item(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_get_next_item\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> __Vtask_get_next_item__3__t;
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_get_next_item(vlProcess, vlSymsp, __Vtask_get_next_item__3__t);
    t = __Vtask_get_next_item__3__t;
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_try_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_try_next_item\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> __Vtask_try_next_item__4__t;
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_try_next_item(vlSymsp, __Vtask_try_next_item__4__t);
    t = __Vtask_try_next_item__4__t;
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_item_done(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_item_done\n"); );
    // Body
    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_item_done(vlProcess, vlSymsp, t);
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_wait_for_sequences(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_wait_for_sequences\n"); );
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_wait_for_sequences(vlSymsp);
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_has_do_available(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &has_do_available__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_has_do_available\n"); );
    // Locals
    CData/*0:0*/ __Vtask_has_do_available__7__Vfuncout;
    __Vtask_has_do_available__7__Vfuncout = 0;
    // Body
    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_has_do_available(vlSymsp, __Vtask_has_do_available__7__Vfuncout);
    has_do_available__Vfuncrtn = __Vtask_has_do_available__7__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_put_response(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_put_response\n"); );
    // Body
    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_put_response(vlProcess, vlSymsp, t);
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_get\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> __Vtask_get__9__t;
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_get(vlSymsp, __Vtask_get__9__t);
    t = __Vtask_get__9__t;
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_peek\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> __Vtask_peek__10__t;
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_peek(vlSymsp, __Vtask_peek__10__t);
    t = __Vtask_peek__10__t;
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::__VnoInFunc_put\n"); );
    // Body
    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::__PVT__m_if, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_sqr_connections.svh", 49)->__VnoInFunc_put(vlSymsp, t);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__print_enabled = 0;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141::to_string_middle\n"); );
    // Body
    std::string out;
    out += "print_enabled:" + VL_TO_STRING(__PVT__print_enabled);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232::to_string_middle();
    return (out);
}
