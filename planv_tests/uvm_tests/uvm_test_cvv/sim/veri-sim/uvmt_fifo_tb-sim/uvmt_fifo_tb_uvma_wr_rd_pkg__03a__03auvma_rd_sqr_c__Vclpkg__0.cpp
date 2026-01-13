// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi179> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi179> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi179__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvma_rd_sqr_c"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi179> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi179__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvma_rd_sqr_c"s;
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz155(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__3__Vfuncout;
    __Vfunc___VBasicRand__3__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__3__Vfuncout);
            }(), __Vfunc___VBasicRand__3__Vfuncout));
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                        uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_sqr_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz155::to_string_middle();
    return (out);
}
