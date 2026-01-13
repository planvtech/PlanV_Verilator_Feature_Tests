// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz182(vlProcess, vlSymsp, name, parent, 1U, 1U, 0xffffffffU) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz182::__PVT__m_if_mask = 0x00000100U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_analysis_export"s;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::__VnoInFunc_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::__VnoInFunc_write\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_size__1__Vfuncout;
    __Vfunc_size__1__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz182> __Vfunc_get_if__2__Vfuncout;
    std::string __Vfunc_get_full_name__4__Vfuncout;
    // Body
    IData/*31:0*/ unnamedblk1__DOT__i;
    unnamedblk1__DOT__i = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_if_base__Tz155_TBz155> tif;
    unnamedblk1__DOT__i = 0U;
    while (VL_LTS_III(32, unnamedblk1__DOT__i, ([&]() {
                    this->__VnoInFunc_size(vlSymsp, __Vfunc_size__1__Vfuncout);
                }(), __Vfunc_size__1__Vfuncout))) {
        this->__VnoInFunc_get_if(vlProcess, vlSymsp, unnamedblk1__DOT__i, __Vfunc_get_if__2__Vfuncout);
        tif = __Vfunc_get_if__2__Vfuncout;
        if ((VlNull{} == tif)) {
            vlSymsp->TOP__uvm_pkg.__VnoInFunc_uvm_report_fatal_TOP__uvm_pkg(vlProcess, vlSymsp, "NTCONN"s, 
                                                                            VL_CVT_PACK_STR_NN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("No uvm_tlm interface is connected to "s, 
                                                                                ([&]() {
                                    this->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vfunc_get_full_name__4__Vfuncout);
                                }(), __Vfunc_get_full_name__4__Vfuncout)), " for executing write()"s)), 0U, ""s, 0U, ""s, 0U);
        }
        VL_NULL_CHECK(tif, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/tlm1/uvm_analysis_port.svh", 153)->__VnoInFunc_write(vlProcess, vlSymsp, t);
        unnamedblk1__DOT__i = ((IData)(1U) + unnamedblk1__DOT__i);
    }
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                    uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_export__Tz155::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz182::to_string_middle();
    return (out);
}
