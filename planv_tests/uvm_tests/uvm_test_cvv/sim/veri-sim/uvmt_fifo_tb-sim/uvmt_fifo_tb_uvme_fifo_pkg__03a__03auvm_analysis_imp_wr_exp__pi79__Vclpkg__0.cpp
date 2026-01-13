// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c> imp)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz181(vlProcess, vlSymsp, name, imp, 2U, 1U, 1U) {
    VL_DEBUG_IF(VL_DBG_MSGF("+              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    this->__PVT__m_imp = imp;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz181::__PVT__m_if_mask = 0x00000100U;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_analysis_imp_wr_exp"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::__VnoInFunc_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::__VnoInFunc_write\n"); );
    // Body
    VL_NULL_CHECK(this->__PVT__m_imp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_sb.svh", 13)->__VnoInFunc_write_wr_exp(vlSymsp, t);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79() {
    VL_DEBUG_IF(VL_DBG_MSGF("+              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+              uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79::to_string_middle\n"); );
    // Body
    std::string out;
    out += "m_imp:" + VL_TO_STRING(__PVT__m_imp);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz181::to_string_middle();
    return (out);
}
