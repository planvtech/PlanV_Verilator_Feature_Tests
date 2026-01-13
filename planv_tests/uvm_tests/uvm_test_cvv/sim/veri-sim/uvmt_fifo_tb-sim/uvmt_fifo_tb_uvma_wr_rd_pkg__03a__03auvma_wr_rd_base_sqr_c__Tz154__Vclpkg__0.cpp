// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi90> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi90> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi90__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvma_wr_rd_base_sqr_c#(SEQ_ITEM)"s;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi90> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__pi90__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvma_wr_rd_base_sqr_c#(SEQ_ITEM)"s;
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc_build_phase\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__3__Vfuncout;
    __Vfunc_uvm_report_enabled__3__Vfuncout = 0;
    CData/*0:0*/ __Vtask_get__5__Vfuncout;
    __Vtask_get__5__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cfg_c> __Vtask_get__5__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__6__Vfuncout;
    __Vfunc_uvm_report_enabled__6__Vfuncout = 0;
    CData/*0:0*/ __Vtask_get__8__Vfuncout;
    __Vtask_get__8__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c> __Vtask_get__8__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__9__Vfuncout;
    __Vfunc_uvm_report_enabled__9__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__11__Vfuncout;
    __Vfunc_uvm_report_enabled__11__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base__pi123::__VnoInFunc_build_phase(vlProcess, vlSymsp, phase);
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "SQR"s, __Vfunc_uvm_report_enabled__3__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__3__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "SQR"s, "Entered build_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_sqr.svh"s, 0x0000002fU, ""s, 1U);
    }
    __Vtask_get__5__value = this->__PVT__cfg;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz158__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154>{this}, ""s, "cfg"s, __Vtask_get__5__value, __Vtask_get__5__Vfuncout);
    this->__PVT__cfg = __Vtask_get__5__value;
    if ((VlNull{} == this->__PVT__cfg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "uvma_wr_rd_base_sqr_c"s, __Vfunc_uvm_report_enabled__6__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__6__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "uvma_wr_rd_base_sqr_c"s, "cfg is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_sqr.svh"s, 0x00000033U, ""s, 1U);
        }
    }
    __Vtask_get__8__value = this->__PVT__cntxt;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz159__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154>{this}, ""s, "cntxt"s, __Vtask_get__8__value, __Vtask_get__8__Vfuncout);
    this->__PVT__cntxt = __Vtask_get__8__value;
    if ((VlNull{} == this->__PVT__cntxt)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "uvma_wr_rd_base_sqr_c"s, __Vfunc_uvm_report_enabled__9__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__9__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "uvma_wr_rd_base_sqr_c"s, "cntxt is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_sqr.svh"s, 0x00000038U, ""s, 1U);
        }
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x000000c8U, 0U, "SQR"s, __Vfunc_uvm_report_enabled__11__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__11__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "SQR"s, "Exiting build_phase"s, 0x000000c8U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvma/uvma_wr_rd/uvma_wr_rd_sqr.svh"s, 0x0000003bU, ""s, 1U);
    }
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__14__Vfuncout;
    __Vfunc___VBasicRand__14__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__14__Vfuncout);
            }(), __Vfunc___VBasicRand__14__Vfuncout));
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154::to_string_middle\n"); );
    // Body
    std::string out;
    out += "cfg:" + VL_TO_STRING(__PVT__cfg);
    out += ", cntxt:" + VL_TO_STRING(__PVT__cntxt);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154::to_string_middle();
    return (out);
}
