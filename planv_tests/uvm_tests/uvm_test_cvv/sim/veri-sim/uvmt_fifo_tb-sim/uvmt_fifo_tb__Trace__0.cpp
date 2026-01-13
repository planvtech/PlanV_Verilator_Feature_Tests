// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Tracing implementation internals

#include "verilated_vcd_c.h"
#include "uvmt_fifo_tb__Syms.h"


void uvmt_fifo_tb___024root__trace_chg_0_sub_0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd::Buffer* bufp);

void uvmt_fifo_tb___024root__trace_chg_0(void* voidSelf, VerilatedVcd::Buffer* bufp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_chg_0\n"); );
    // Body
    uvmt_fifo_tb___024root* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<uvmt_fifo_tb___024root*>(voidSelf);
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    if (VL_UNLIKELY(!vlSymsp->__Vm_activity)) return;
    uvmt_fifo_tb___024root__trace_chg_0_sub_0((&vlSymsp->TOP), bufp);
}

void uvmt_fifo_tb___024root__trace_chg_0_sub_0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd::Buffer* bufp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_chg_0_sub_0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    uint32_t* const oldp VL_ATTR_UNUSED = bufp->oldp(vlSymsp->__Vm_baseCode + 1);
    if (VL_UNLIKELY((vlSelfRef.__Vm_traceActivity[0U]))) {
        bufp->chgIData(oldp+0,(vlSelfRef.uvmt_fifo_tb__DOT__tb_end_of_test__DOT__err_count),32);
        bufp->chgIData(oldp+1,(vlSelfRef.uvmt_fifo_tb__DOT__tb_end_of_test__DOT__warning_count),32);
        bufp->chgIData(oldp+2,(vlSelfRef.uvmt_fifo_tb__DOT__tb_end_of_test__DOT__fatal_count),32);
        bufp->chgBit(oldp+3,(vlSelfRef.uvmt_fifo_tb__DOT__tb_end_of_test__DOT__sim_finished));
        bufp->chgIData(oldp+4,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_global_random_seed),32);
    }
    if (VL_UNLIKELY((vlSelfRef.__Vm_traceActivity[1U]))) {
        bufp->chgBit(oldp+5,(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.start_clk));
        bufp->chgDouble(oldp+6,(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.clk_period));
        bufp->chgBit(oldp+8,(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.start_clk));
        bufp->chgDouble(oldp+9,(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.clk_period));
    }
    if (VL_UNLIKELY(((vlSelfRef.__Vm_traceActivity[2U] 
                      | vlSelfRef.__Vm_traceActivity
                      [5U])))) {
        bufp->chgCData(oldp+11,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[0]),8);
        bufp->chgCData(oldp+12,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[1]),8);
        bufp->chgCData(oldp+13,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[2]),8);
        bufp->chgCData(oldp+14,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[3]),8);
        bufp->chgCData(oldp+15,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[4]),8);
        bufp->chgCData(oldp+16,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[5]),8);
        bufp->chgCData(oldp+17,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[6]),8);
        bufp->chgCData(oldp+18,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[7]),8);
        bufp->chgCData(oldp+19,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[8]),8);
        bufp->chgCData(oldp+20,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[9]),8);
        bufp->chgCData(oldp+21,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[10]),8);
        bufp->chgCData(oldp+22,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[11]),8);
        bufp->chgCData(oldp+23,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[12]),8);
        bufp->chgCData(oldp+24,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[13]),8);
        bufp->chgCData(oldp+25,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[14]),8);
        bufp->chgCData(oldp+26,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[15]),8);
    }
    if (VL_UNLIKELY(((vlSelfRef.__Vm_traceActivity[2U] 
                      | vlSelfRef.__Vm_traceActivity
                      [6U])))) {
        bufp->chgCData(oldp+27,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_gray_next),5);
        bufp->chgCData(oldp+28,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__r_ptr_gray_next),5);
        bufp->chgBit(oldp+29,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_full_tmp));
        bufp->chgCData(oldp+30,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin_next),5);
        bufp->chgCData(oldp+31,(vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.data),8);
    }
    if (VL_UNLIKELY((vlSelfRef.__Vm_traceActivity[3U]))) {
        bufp->chgBit(oldp+32,(vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__r_empty));
        bufp->chgCData(oldp+33,((0x0000000fU & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin))),4);
        bufp->chgCData(oldp+34,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_i),5);
        bufp->chgCData(oldp+35,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_o),5);
        bufp->chgCData(oldp+36,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin),5);
        bufp->chgCData(oldp+37,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_sync__DOT__ptr_temp),5);
        bufp->chgBit(oldp+38,(vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.empty));
    }
    if (VL_UNLIKELY((vlSelfRef.__Vm_traceActivity[4U]))) {
        bufp->chgBit(oldp+39,(vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__w_full));
        bufp->chgCData(oldp+40,((0x0000000fU & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin))),4);
        bufp->chgCData(oldp+41,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_i),5);
        bufp->chgCData(oldp+42,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_o),5);
        bufp->chgCData(oldp+43,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin),5);
        bufp->chgCData(oldp+44,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_sync__DOT__ptr_temp),5);
        bufp->chgBit(oldp+45,(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.full));
    }
    if (VL_UNLIKELY((vlSelfRef.__Vm_traceActivity[7U]))) {
        bufp->chgCData(oldp+46,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_leaf_scope__Vstatic__bracket_match),8);
        bufp->chgIData(oldp+47,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_leaf_scope__Vstatic__pos),32);
        bufp->chgIData(oldp+48,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_leaf_scope__Vstatic__bmatches),32);
    }
    bufp->chgBit(oldp+49,(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.clk));
    bufp->chgBit(oldp+50,(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.reset_n));
    bufp->chgBit(oldp+51,(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.clk));
    bufp->chgBit(oldp+52,(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.reset_n));
    bufp->chgCData(oldp+53,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data
                            [(0x0000000fU & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin))]),8);
    bufp->chgCData(oldp+54,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_gray_next),5);
    bufp->chgCData(oldp+55,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin_next),5);
    bufp->chgBit(oldp+56,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_empty_tmp));
    bufp->chgIData(oldp+57,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_re_match__Vstatic__e),32);
    bufp->chgIData(oldp+58,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_re_match__Vstatic__es),32);
    bufp->chgIData(oldp+59,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_re_match__Vstatic__s),32);
    bufp->chgIData(oldp+60,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_re_match__Vstatic__ss),32);
    bufp->chgIData(oldp+61,(vlSymsp->TOP__uvm_pkg.__PVT__m_uvm_core_state),32);
    bufp->chgCData(oldp+62,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_instance_scope__Vstatic__c),8);
    bufp->chgIData(oldp+63,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_instance_scope__Vstatic__pos),32);
    bufp->chgBit(oldp+64,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_oneway_hash__Vstatic__msb));
    bufp->chgCData(oldp+65,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_oneway_hash__Vstatic__current_byte),8);
    bufp->chgIData(oldp+66,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_oneway_hash__Vstatic__crc1),32);
    bufp->chgIData(oldp+67,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_wait_for_nba_region__Vstatic__next_nba),32);
    bufp->chgBit(oldp+68,(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.clk));
    bufp->chgBit(oldp+69,(vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.clk));
}

void uvmt_fifo_tb___024root__trace_cleanup(void* voidSelf, VerilatedVcd* /*unused*/) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_cleanup\n"); );
    // Body
    uvmt_fifo_tb___024root* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<uvmt_fifo_tb___024root*>(voidSelf);
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    vlSymsp->__Vm_activity = false;
    vlSymsp->TOP.__Vm_traceActivity[0U] = 0U;
    vlSymsp->TOP.__Vm_traceActivity[1U] = 0U;
    vlSymsp->TOP.__Vm_traceActivity[2U] = 0U;
    vlSymsp->TOP.__Vm_traceActivity[3U] = 0U;
    vlSymsp->TOP.__Vm_traceActivity[4U] = 0U;
    vlSymsp->TOP.__Vm_traceActivity[5U] = 0U;
    vlSymsp->TOP.__Vm_traceActivity[6U] = 0U;
    vlSymsp->TOP.__Vm_traceActivity[7U] = 0U;
}
