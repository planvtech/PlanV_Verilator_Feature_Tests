// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi93> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi93> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi93__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvma_rd_random_seq_c"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi93> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi93__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c, vlProcess, vlSymsp, "uvma_rd_random_seq"s)
            : VL_NEW(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvma_rd_random_seq_c"s;
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

VlCoroutine uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_body(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_body\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> __Vfunc_create__4__Vfuncout;
    IData/*31:0*/ __Vtask_randomize__6__Vfuncout;
    __Vtask_randomize__6__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> seq_item;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi88__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "seq_item"s, VlNull{}, ""s, __Vfunc_create__4__Vfuncout);
    seq_item = __Vfunc_create__4__Vfuncout;
    co_await this->__VnoInFunc_start_item(vlProcess, vlSymsp, seq_item, 0xffffffffU, VlNull{});
    VL_NULL_CHECK(seq_item, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/seq/uvma_wr_rd_random_seq.svh", 63)->__VnoInFunc_randomize(vlSymsp, __Vtask_randomize__6__Vfuncout);
    co_await this->__VnoInFunc_finish_item(vlProcess, vlSymsp, seq_item, 0xffffffffU);
    co_return;}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__9__Vfuncout;
    __Vfunc___VBasicRand__9__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__9__Vfuncout);
            }(), __Vfunc___VBasicRand__9__Vfuncout));
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::to_string_middle();
    return (out);
}
