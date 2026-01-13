// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz154> imp)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz181(vlProcess, vlSymsp, name, imp, 2U, 1U, 1U) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    this->__PVT__m_imp = imp;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz181::__PVT__m_if_mask = 0x00000066U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_get_peek_imp"s;
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_get\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> __Vtask_get__1__t;
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_imps.svh", 152)->__VnoInFunc_get(vlSymsp, __Vtask_get__1__t);
    t = __Vtask_get__1__t;
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_peek\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> __Vtask_peek__2__t;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_imps.svh", 152)->__VnoInFunc_peek(vlProcess, vlSymsp, __Vtask_peek__2__t);
    t = __Vtask_peek__2__t;
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_try_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t, CData/*0:0*/ &try_get__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_try_get\n"); );
    // Locals
    CData/*0:0*/ __Vtask_try_get__3__Vfuncout;
    __Vtask_try_get__3__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> __Vtask_try_get__3__t;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_imps.svh", 152)->__VnoInFunc_try_get(vlProcess, vlSymsp, __Vtask_try_get__3__t, __Vtask_try_get__3__Vfuncout);
    t = __Vtask_try_get__3__t;
    try_get__Vfuncrtn = __Vtask_try_get__3__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_can_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_get__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_can_get\n"); );
    // Locals
    CData/*0:0*/ __Vtask_can_get__4__Vfuncout;
    __Vtask_can_get__4__Vfuncout = 0;
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_imps.svh", 152)->__VnoInFunc_can_get(vlSymsp, __Vtask_can_get__4__Vfuncout);
    can_get__Vfuncrtn = __Vtask_can_get__4__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_try_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t, CData/*0:0*/ &try_peek__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_try_peek\n"); );
    // Locals
    CData/*0:0*/ __Vtask_try_peek__5__Vfuncout;
    __Vtask_try_peek__5__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> __Vtask_try_peek__5__t;
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_imps.svh", 152)->__VnoInFunc_try_peek(vlSymsp, __Vtask_try_peek__5__t, __Vtask_try_peek__5__Vfuncout);
    t = __Vtask_try_peek__5__t;
    try_peek__Vfuncrtn = __Vtask_try_peek__5__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_can_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_peek__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::__VnoInFunc_can_peek\n"); );
    // Locals
    CData/*0:0*/ __Vtask_can_peek__6__Vfuncout;
    __Vtask_can_peek__6__Vfuncout = 0;
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_imps.svh", 152)->__VnoInFunc_can_peek(vlSymsp, __Vtask_can_peek__6__Vfuncout);
    can_peek__Vfuncrtn = __Vtask_can_peek__6__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz154_TBz293::to_string_middle\n"); );
    // Body
    std::string out;
    out += "m_imp:" + VL_TO_STRING(__PVT__m_imp);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz181::to_string_middle();
    return (out);
}
