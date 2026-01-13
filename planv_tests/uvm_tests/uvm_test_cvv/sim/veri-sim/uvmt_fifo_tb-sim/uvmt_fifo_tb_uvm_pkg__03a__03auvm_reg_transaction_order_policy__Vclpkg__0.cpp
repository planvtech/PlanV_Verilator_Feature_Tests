// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_object(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::__VnoInFunc_order(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<uvmt_fifo_tb_uvm_reg_bus_op__struct__0> &q) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::__VnoInFunc_order\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__2__Vfuncout;
    __Vfunc___VBasicRand__2__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__2__Vfuncout);
            }(), __Vfunc___VBasicRand__2__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_transaction_order_policy::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::to_string_middle();
    return (out);
}
