// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz155> imp)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz182(vlProcess, vlSymsp, name, imp, 2U, 1U, 1U) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    this->__PVT__m_imp = imp;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz182::__PVT__m_if_mask = 0x00000011U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_put_imp"s;
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::__VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::__VnoInFunc_put\n"); );
    // Body
    VL_KEEP_THIS;
    co_await VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_imps.svh", 98)->__VnoInFunc_put(vlSymsp, t);
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::__VnoInFunc_try_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> t, CData/*0:0*/ &try_put__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::__VnoInFunc_try_put\n"); );
    // Locals
    CData/*0:0*/ __Vtask_try_put__2__Vfuncout;
    __Vtask_try_put__2__Vfuncout = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_imps.svh", 98)->__VnoInFunc_try_put(vlProcess, vlSymsp, t, __Vtask_try_put__2__Vfuncout);
    try_put__Vfuncrtn = __Vtask_try_put__2__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::__VnoInFunc_can_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_put__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::__VnoInFunc_can_put\n"); );
    // Locals
    CData/*0:0*/ __Vtask_can_put__3__Vfuncout;
    __Vtask_can_put__3__Vfuncout = 0;
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_imps.svh", 98)->__VnoInFunc_can_put(vlSymsp, __Vtask_can_put__3__Vfuncout);
    can_put__Vfuncrtn = __Vtask_can_put__3__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz155_TBz295::to_string_middle\n"); );
    // Body
    std::string out;
    out += "m_imp:" + VL_TO_STRING(__PVT__m_imp);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz182::to_string_middle();
    return (out);
}
