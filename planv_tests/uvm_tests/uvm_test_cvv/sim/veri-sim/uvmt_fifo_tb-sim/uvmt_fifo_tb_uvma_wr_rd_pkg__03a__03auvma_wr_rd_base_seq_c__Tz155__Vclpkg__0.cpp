// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi128> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi128> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi128__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvma_wr_rd_base_seq_c"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi128> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi128__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c_> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c_, vlProcess, vlSymsp, "uvma_wr_rd_base_seq"s)
            : VL_NEW(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c_, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvma_wr_rd_base_seq_c"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_m_set_p_sequencer(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_m_set_p_sequencer\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__4__Vfuncout;
    __Vfunc_uvm_report_enabled__4__Vfuncout = 0;
    std::string __Vfunc_get_full_name__6__Vfuncout;
    std::string __Vtemp_1;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__VnoInFunc_m_set_p_sequencer(vlProcess, vlSymsp);
    if ((! VL_CAST_DYNAMIC(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer, this->__PVT__p_sequencer))) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "DCLPSQ"s, __Vfunc_uvm_report_enabled__4__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__4__Vfuncout))) {
            __Vtemp_1 = ([&]() {
                    this->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vfunc_get_full_name__6__Vfuncout);
                }(), __Vfunc_get_full_name__6__Vfuncout);
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "DCLPSQ"s, VL_SFORMATF_N_NX("%Nuvma_wr_rd_pkg.uvma_wr_rd_base_seq_c__Tz155.m_set_p_sequencer %@ Error casting p_sequencer, please verify that this sequence/sequence item is intended to execute on this type of sequencer",0,
                                                                                vlSymsp->name(),
                                                                                -1,
                                                                                &(__Vtemp_1)) , 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/seq/uvma_wr_rd_base_seq.svh"s, 0x00000010U, ""s, 1U);
        }
    }
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence__Tz155_TBz155(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc_randomize\n"); );
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

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_seq_c__Tz155::to_string_middle\n"); );
    // Body
    std::string out;
    out += "p_sequencer:" + VL_TO_STRING(__PVT__p_sequencer);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence__Tz155_TBz155::to_string_middle();
    return (out);
}
