// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz154(vlProcess, vlSymsp, name, parent, 0U) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    this->__PVT__analysis_export = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_imp__Tz154_TBz284, vlProcess, vlSymsp, "analysis_export"s, 
                                          VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148>{this});
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::__VnoInFunc_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::__VnoInFunc_write\n"); );
    // Body
    if ((VlNull{} == this->__PVT__sequencer_ptr)) {
        this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "SEQRNULL"s, "The sequencer pointer is null when attempting a write"s, 0U, ""s, 0U, ""s, 0U);
    }
    VL_NULL_CHECK(this->__PVT__sequencer_ptr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer_analysis_fifo.svh", 36)->__VnoInFunc_analysis_write(vlProcess, vlSymsp, t);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__5__Vfuncout;
    __Vfunc___VBasicRand__5__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__5__Vfuncout);
            }(), __Vfunc___VBasicRand__5__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_analysis_fifo__pi148::to_string_middle\n"); );
    // Body
    std::string out;
    out += "analysis_export:" + VL_TO_STRING(__PVT__analysis_export);
    out += ", sequencer_ptr:" + VL_TO_STRING(__PVT__sequencer_ptr);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz154::to_string_middle();
    return (out);
}
