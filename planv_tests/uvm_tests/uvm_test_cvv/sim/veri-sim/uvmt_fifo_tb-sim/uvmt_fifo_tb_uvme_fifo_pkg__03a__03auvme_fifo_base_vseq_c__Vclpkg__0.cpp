// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi83> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi83> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi83__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvme_fifo_base_vseq_c"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi83> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi83__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c, vlProcess, vlSymsp, "uvme_fifo_base_vseq_c"s)
            : VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvme_fifo_base_vseq_c"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_m_set_p_sequencer(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_m_set_p_sequencer\n"); );
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
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "DCLPSQ"s, VL_SFORMATF_N_NX("%Nuvme_fifo_pkg.uvme_fifo_base_vseq_c.m_set_p_sequencer %@ Error casting p_sequencer, please verify that this sequence/sequence item is intended to execute on this type of sequencer",0,
                                                                                vlSymsp->name(),
                                                                                -1,
                                                                                &(__Vtemp_1)) , 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_base_vseq.svh"s, 0x00000015U, ""s, 1U);
        }
    }
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_pre_start(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_pre_start\n"); );
    // Body
    this->__PVT__cfg = VL_NULL_CHECK(this->__PVT__p_sequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_base_vseq.svh", 39)
        ->__PVT__cfg;
    this->__PVT__cntxt = VL_NULL_CHECK(this->__PVT__p_sequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/vseq/uvme_fifo_base_vseq.svh", 40)
        ->__PVT__cntxt;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc_randomize\n"); );
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

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_base_vseq_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += "cfg:" + VL_TO_STRING(__PVT__cfg);
    out += ", cntxt:" + VL_TO_STRING(__PVT__cntxt);
    out += ", p_sequencer:" + VL_TO_STRING(__PVT__p_sequencer);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::to_string_middle();
    return (out);
}
