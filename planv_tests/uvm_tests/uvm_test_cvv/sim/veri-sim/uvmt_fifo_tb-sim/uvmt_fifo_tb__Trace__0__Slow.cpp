// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Tracing implementation internals

#include "verilated_vcd_c.h"
#include "uvmt_fifo_tb__Syms.h"


VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvm_pkg__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep);
VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep);
VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep);
VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__write_if__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep);
VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__read_if__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep);

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_init_sub__TOP__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    const int c = vlSymsp->__Vm_baseCode;
    tracep->pushPrefix("uvm_pkg", VerilatedTracePrefixType::SCOPE_MODULE);
    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvm_pkg__0(vlSelf, tracep);
    tracep->popPrefix();
    tracep->pushPrefix("uvmt_fifo_tb", VerilatedTracePrefixType::SCOPE_MODULE);
    tracep->pushPrefix("wr_clk_gen_if", VerilatedTracePrefixType::SCOPE_INTERFACE);
    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__0(vlSelf, tracep);
    tracep->popPrefix();
    tracep->pushPrefix("rd_clk_gen_if", VerilatedTracePrefixType::SCOPE_INTERFACE);
    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__0(vlSelf, tracep);
    tracep->popPrefix();
    tracep->pushPrefix("write_if", VerilatedTracePrefixType::SCOPE_INTERFACE);
    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__write_if__0(vlSelf, tracep);
    tracep->popPrefix();
    tracep->pushPrefix("read_if", VerilatedTracePrefixType::SCOPE_INTERFACE);
    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__read_if__0(vlSelf, tracep);
    tracep->popPrefix();
    tracep->pushPrefix("simple_demo_tb", VerilatedTracePrefixType::SCOPE_MODULE);
    tracep->declBit(c+50,0,"w_clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+51,0,"w_rst",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+71,0,"w_en",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+52,0,"r_clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+53,0,"r_rst",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+72,0,"r_en",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+73,0,"w_data",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 7,0);
    tracep->declBus(c+54,0,"r_data",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 7,0);
    tracep->declBit(c+40,0,"w_full",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+33,0,"r_empty",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+74,0,"DATA_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+75,0,"ADDR_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->pushPrefix("dut", VerilatedTracePrefixType::SCOPE_MODULE);
    tracep->declBus(c+74,0,"DATA_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+75,0,"ADDR_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+54,0,"r_data",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 7,0);
    tracep->declBit(c+40,0,"w_full",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+33,0,"r_empty",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+73,0,"w_data",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 7,0);
    tracep->declBit(c+71,0,"w_en",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+51,0,"w_rst",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+50,0,"w_clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+72,0,"r_en",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+52,0,"r_clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+53,0,"r_rst",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+41,0,"w_addr",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 3,0);
    tracep->declBus(c+34,0,"r_addr",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 3,0);
    tracep->declBus(c+42,0,"w_ptr_i",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+35,0,"r_ptr_i",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+43,0,"w_ptr_o",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+36,0,"r_ptr_o",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->pushPrefix("fifo_mem", VerilatedTracePrefixType::SCOPE_MODULE);
    tracep->declBus(c+75,0,"ADDR_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+74,0,"DATA_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+54,0,"r_data",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 7,0);
    tracep->declBus(c+34,0,"r_addr",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 3,0);
    tracep->declBus(c+73,0,"w_data",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 7,0);
    tracep->declBit(c+71,0,"w_en",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+50,0,"w_clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+40,0,"w_full",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+41,0,"w_addr",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 3,0);
    tracep->declBus(c+76,0,"DEPTH",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->pushPrefix("fifo_data", VerilatedTracePrefixType::ARRAY_UNPACKED);
    for (int i = 0; i < 16; ++i) {
        tracep->declBus(c+12+i*1,0,"",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, true,(i+0), 7,0);
    }
    tracep->popPrefix();
    tracep->popPrefix();
    tracep->pushPrefix("r_empty_checker", VerilatedTracePrefixType::SCOPE_MODULE);
    tracep->declBus(c+75,0,"ADDR_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBit(c+33,0,"r_empty",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+35,0,"r_ptr_gray",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+34,0,"r_addr",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 3,0);
    tracep->declBus(c+43,0,"w_ptr_gray",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBit(c+72,0,"r_en",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+52,0,"r_clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+53,0,"r_rst",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+55,0,"r_ptr_gray_next",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+37,0,"r_ptr_bin",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+56,0,"r_ptr_bin_next",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBit(c+57,0,"r_empty_tmp",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->popPrefix();
    tracep->pushPrefix("r_sync", VerilatedTracePrefixType::SCOPE_MODULE);
    tracep->declBus(c+75,0,"ADDR_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+35,0,"i_ptr",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+36,0,"o_ptr",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBit(c+52,0,"clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+53,0,"rst",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+38,0,"ptr_temp",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->popPrefix();
    tracep->pushPrefix("w_full_checker", VerilatedTracePrefixType::SCOPE_MODULE);
    tracep->declBus(c+75,0,"ADDR_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+36,0,"r_ptr_gray",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBit(c+50,0,"w_clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+51,0,"w_rst",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+71,0,"w_en",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+41,0,"w_addr",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 3,0);
    tracep->declBit(c+40,0,"w_full",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+42,0,"w_ptr_gray",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+28,0,"w_ptr_gray_next",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+29,0,"r_ptr_gray_next",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBit(c+30,0,"w_full_tmp",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+44,0,"w_ptr_bin",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+31,0,"w_ptr_bin_next",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->popPrefix();
    tracep->pushPrefix("w_sync", VerilatedTracePrefixType::SCOPE_MODULE);
    tracep->declBus(c+75,0,"ADDR_SIZE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+42,0,"i_ptr",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBus(c+43,0,"o_ptr",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->declBit(c+50,0,"clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+51,0,"rst",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+45,0,"ptr_temp",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 4,0);
    tracep->popPrefix();
    tracep->popPrefix();
    tracep->popPrefix();
    tracep->pushPrefix("tb_end_of_test", VerilatedTracePrefixType::SCOPE_MODULE);
    tracep->declBus(c+1,0,"err_count",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+2,0,"warning_count",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+3,0,"fatal_count",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBit(c+4,0,"sim_finished",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::BIT, false,-1);
    tracep->popPrefix();
    tracep->popPrefix();
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvm_pkg__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvm_pkg__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    const int c = vlSymsp->__Vm_baseCode;
    tracep->declBus(c+77,0,"UVM_HDL_MAX_WIDTH",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+58,0,"uvm_re_match__Vstatic__e",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+59,0,"uvm_re_match__Vstatic__es",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+60,0,"uvm_re_match__Vstatic__s",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+61,0,"uvm_re_match__Vstatic__ss",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+78,0,"UVM_STREAMBITS",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+79,0,"UVM_FIELD_FLAG_RESERVED_BITS",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+80,0,"UVM_RADIX",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+81,0,"UVM_RECURSION",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 27,0);
    tracep->declBus(c+82,0,"UVM_MACRO_NUMFLAGS",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+83,0,"UVM_DEFAULT",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+84,0,"UVM_ALL_ON",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+84,0,"UVM_FLAGS_ON",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+85,0,"UVM_FLAGS_OFF",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+86,0,"UVM_COPY",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+87,0,"UVM_NOCOPY",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+88,0,"UVM_COMPARE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+89,0,"UVM_NOCOMPARE",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+90,0,"UVM_PRINT",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+91,0,"UVM_NOPRINT",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+92,0,"UVM_RECORD",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+93,0,"UVM_NORECORD",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+94,0,"UVM_PACK",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+95,0,"UVM_NOPACK",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+96,0,"UVM_UNPACK",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+95,0,"UVM_NOUNPACK",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+97,0,"UVM_SET",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+98,0,"UVM_NOSET",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+99,0,"UVM_NODEFPRINT",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+100,0,"UVM_MACRO_EXTRAS",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+101,0,"UVM_FLAGS",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+102,0,"UVM_CHECK_FIELDS",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+103,0,"UVM_END_DATA_EXTRA",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+104,0,"UVM_START_FUNCS",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+105,0,"UVM_END_FUNCS",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::BIT, false,-1, 27,0);
    tracep->declBus(c+106,0,"UVM_STDIN",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+107,0,"UVM_STDOUT",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+108,0,"UVM_STDERR",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+62,0,"m_uvm_core_state",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+109,0,"UVM_CORE_POST_INIT",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+5,0,"uvm_global_random_seed",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+63,0,"uvm_instance_scope__Vstatic__c",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::BYTE, false,-1, 7,0);
    tracep->declBus(c+64,0,"uvm_instance_scope__Vstatic__pos",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+110,0,"UVM_STR_CRC_POLYNOMIAL",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBit(c+65,0,"uvm_oneway_hash__Vstatic__msb",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::BIT, false,-1);
    tracep->declBus(c+66,0,"uvm_oneway_hash__Vstatic__current_byte",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::BIT, false,-1, 7,0);
    tracep->declBus(c+67,0,"uvm_oneway_hash__Vstatic__crc1",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::BIT, false,-1, 31,0);
    tracep->declBus(c+47,0,"uvm_leaf_scope__Vstatic__bracket_match",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::BYTE, false,-1, 7,0);
    tracep->declBus(c+48,0,"uvm_leaf_scope__Vstatic__pos",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+49,0,"uvm_leaf_scope__Vstatic__bmatches",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+111,0,"uvm_get_array_index_int__Vstatic__i",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+112,0,"uvm_get_array_index_string__Vstatic__i",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+113,0,"UVM_LINE_WIDTH",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+113,0,"UVM_NUM_LINES",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+114,0,"UVM_SMALL_STRING",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+115,0,"UVM_LARGE_STRING",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::PARAMETER, VerilatedTraceSigType::LOGIC, false,-1, 31,0);
    tracep->declBus(c+68,0,"uvm_wait_for_nba_region__Vstatic__next_nba",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
    tracep->declBus(c+116,0,"UVM_UNBOUNDED_CONNECTIONS",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::INT, false,-1, 31,0);
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    const int c = vlSymsp->__Vm_baseCode;
    tracep->declBit(c+50,0,"clk",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+51,0,"reset_n",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+6,0,"start_clk",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::BIT, false,-1);
    tracep->declDouble(c+7,0,"clk_period",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::DOUBLE, false,-1);
    tracep->declDouble(c+117,0,"reset_deassert_duration",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::DOUBLE, false,-1);
    tracep->declDouble(c+117,0,"reset_assert_duration",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::DOUBLE, false,-1);
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    const int c = vlSymsp->__Vm_baseCode;
    tracep->declBit(c+52,0,"clk",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+53,0,"reset_n",-1, VerilatedTraceSigDirection::OUTPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+9,0,"start_clk",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::BIT, false,-1);
    tracep->declDouble(c+10,0,"clk_period",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::DOUBLE, false,-1);
    tracep->declDouble(c+117,0,"reset_deassert_duration",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::DOUBLE, false,-1);
    tracep->declDouble(c+117,0,"reset_assert_duration",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::DOUBLE, false,-1);
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__write_if__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__write_if__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    const int c = vlSymsp->__Vm_baseCode;
    tracep->declBit(c+69,0,"clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+51,0,"reset_n",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+73,0,"data",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 7,0);
    tracep->declBit(c+71,0,"en",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+46,0,"full",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1);
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__read_if__0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_init_sub__TOP__uvmt_fifo_tb__DOT__read_if__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    const int c = vlSymsp->__Vm_baseCode;
    tracep->declBit(c+70,0,"clk",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+53,0,"reset_n",-1, VerilatedTraceSigDirection::INPUT, VerilatedTraceSigKind::WIRE, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBus(c+32,0,"data",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1, 7,0);
    tracep->declBit(c+72,0,"en",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1);
    tracep->declBit(c+39,0,"empty",-1, VerilatedTraceSigDirection::NONE, VerilatedTraceSigKind::VAR, VerilatedTraceSigType::LOGIC, false,-1);
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_init_top(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_init_top\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    uvmt_fifo_tb___024root__trace_init_sub__TOP__0(vlSelf, tracep);
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_const_0(void* voidSelf, VerilatedVcd::Buffer* bufp);
VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_full_0(void* voidSelf, VerilatedVcd::Buffer* bufp);
void uvmt_fifo_tb___024root__trace_chg_0(void* voidSelf, VerilatedVcd::Buffer* bufp);
void uvmt_fifo_tb___024root__trace_cleanup(void* voidSelf, VerilatedVcd* /*unused*/);

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_register(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd* tracep) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_register\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    tracep->addConstCb(&uvmt_fifo_tb___024root__trace_const_0, 0, vlSelf);
    tracep->addFullCb(&uvmt_fifo_tb___024root__trace_full_0, 0, vlSelf);
    tracep->addChgCb(&uvmt_fifo_tb___024root__trace_chg_0, 0, vlSelf);
    tracep->addCleanupCb(&uvmt_fifo_tb___024root__trace_cleanup, vlSelf);
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_const_0_sub_0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd::Buffer* bufp);

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_const_0(void* voidSelf, VerilatedVcd::Buffer* bufp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_const_0\n"); );
    // Body
    uvmt_fifo_tb___024root* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<uvmt_fifo_tb___024root*>(voidSelf);
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    uvmt_fifo_tb___024root__trace_const_0_sub_0((&vlSymsp->TOP), bufp);
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_const_0_sub_0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd::Buffer* bufp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_const_0_sub_0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    uint32_t* const oldp VL_ATTR_UNUSED = bufp->oldp(vlSymsp->__Vm_baseCode);
    bufp->fullBit(oldp+71,(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.en));
    bufp->fullBit(oldp+72,(vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.en));
    bufp->fullCData(oldp+73,(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.data),8);
    bufp->fullIData(oldp+74,(8U),32);
    bufp->fullIData(oldp+75,(4U),32);
    bufp->fullIData(oldp+76,(0x00000010U),32);
    bufp->fullIData(oldp+77,(0x00000400U),32);
    bufp->fullIData(oldp+78,(0x00001000U),32);
    bufp->fullIData(oldp+79,(0x0000001cU),32);
    bufp->fullIData(oldp+80,(0x0f000000U),32);
    bufp->fullIData(oldp+81,(0x00070000U),28);
    bufp->fullIData(oldp+82,(0x00000013U),28);
    bufp->fullIData(oldp+83,(0x00000555U),28);
    bufp->fullIData(oldp+84,(0x00000155U),28);
    bufp->fullIData(oldp+85,(0U),28);
    bufp->fullIData(oldp+86,(1U),28);
    bufp->fullIData(oldp+87,(2U),28);
    bufp->fullIData(oldp+88,(4U),28);
    bufp->fullIData(oldp+89,(8U),28);
    bufp->fullIData(oldp+90,(0x00000010U),28);
    bufp->fullIData(oldp+91,(0x00000020U),28);
    bufp->fullIData(oldp+92,(0x00000040U),28);
    bufp->fullIData(oldp+93,(0x00000080U),28);
    bufp->fullIData(oldp+94,(0x00000100U),28);
    bufp->fullIData(oldp+95,(0x00000200U),28);
    bufp->fullIData(oldp+96,(0x00000400U),28);
    bufp->fullIData(oldp+97,(0x00000800U),28);
    bufp->fullIData(oldp+98,(0x00001000U),28);
    bufp->fullIData(oldp+99,(0x00008000U),28);
    bufp->fullIData(oldp+100,(0x00080000U),28);
    bufp->fullIData(oldp+101,(0x00080001U),28);
    bufp->fullIData(oldp+102,(0x00080002U),28);
    bufp->fullIData(oldp+103,(0x00080003U),28);
    bufp->fullIData(oldp+104,(0x00080004U),28);
    bufp->fullIData(oldp+105,(0x00080005U),28);
    bufp->fullIData(oldp+106,(0x80000000U),32);
    bufp->fullIData(oldp+107,(0x80000001U),32);
    bufp->fullIData(oldp+108,(0x80000002U),32);
    bufp->fullIData(oldp+109,(3U),32);
    bufp->fullIData(oldp+110,(0x04c11db6U),32);
    bufp->fullIData(oldp+111,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_get_array_index_int__Vstatic__i),32);
    bufp->fullIData(oldp+112,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_get_array_index_string__Vstatic__i),32);
    bufp->fullIData(oldp+113,(0x00000078U),32);
    bufp->fullIData(oldp+114,(0x000003bfU),32);
    bufp->fullIData(oldp+115,(0x0001c1ffU),32);
    bufp->fullIData(oldp+116,(0xffffffffU),32);
    bufp->fullDouble(oldp+117,(6.99999999999999911e+00));
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_full_0_sub_0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd::Buffer* bufp);

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_full_0(void* voidSelf, VerilatedVcd::Buffer* bufp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_full_0\n"); );
    // Body
    uvmt_fifo_tb___024root* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<uvmt_fifo_tb___024root*>(voidSelf);
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    uvmt_fifo_tb___024root__trace_full_0_sub_0((&vlSymsp->TOP), bufp);
}

VL_ATTR_COLD void uvmt_fifo_tb___024root__trace_full_0_sub_0(uvmt_fifo_tb___024root* vlSelf, VerilatedVcd::Buffer* bufp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root__trace_full_0_sub_0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    uint32_t* const oldp VL_ATTR_UNUSED = bufp->oldp(vlSymsp->__Vm_baseCode);
    bufp->fullIData(oldp+1,(vlSelfRef.uvmt_fifo_tb__DOT__tb_end_of_test__DOT__err_count),32);
    bufp->fullIData(oldp+2,(vlSelfRef.uvmt_fifo_tb__DOT__tb_end_of_test__DOT__warning_count),32);
    bufp->fullIData(oldp+3,(vlSelfRef.uvmt_fifo_tb__DOT__tb_end_of_test__DOT__fatal_count),32);
    bufp->fullBit(oldp+4,(vlSelfRef.uvmt_fifo_tb__DOT__tb_end_of_test__DOT__sim_finished));
    bufp->fullIData(oldp+5,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_global_random_seed),32);
    bufp->fullBit(oldp+6,(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.start_clk));
    bufp->fullDouble(oldp+7,(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.clk_period));
    bufp->fullBit(oldp+9,(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.start_clk));
    bufp->fullDouble(oldp+10,(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.clk_period));
    bufp->fullCData(oldp+12,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[0]),8);
    bufp->fullCData(oldp+13,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[1]),8);
    bufp->fullCData(oldp+14,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[2]),8);
    bufp->fullCData(oldp+15,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[3]),8);
    bufp->fullCData(oldp+16,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[4]),8);
    bufp->fullCData(oldp+17,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[5]),8);
    bufp->fullCData(oldp+18,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[6]),8);
    bufp->fullCData(oldp+19,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[7]),8);
    bufp->fullCData(oldp+20,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[8]),8);
    bufp->fullCData(oldp+21,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[9]),8);
    bufp->fullCData(oldp+22,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[10]),8);
    bufp->fullCData(oldp+23,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[11]),8);
    bufp->fullCData(oldp+24,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[12]),8);
    bufp->fullCData(oldp+25,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[13]),8);
    bufp->fullCData(oldp+26,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[14]),8);
    bufp->fullCData(oldp+27,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[15]),8);
    bufp->fullCData(oldp+28,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_gray_next),5);
    bufp->fullCData(oldp+29,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__r_ptr_gray_next),5);
    bufp->fullBit(oldp+30,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_full_tmp));
    bufp->fullCData(oldp+31,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin_next),5);
    bufp->fullCData(oldp+32,(vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.data),8);
    bufp->fullBit(oldp+33,(vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__r_empty));
    bufp->fullCData(oldp+34,((0x0000000fU & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin))),4);
    bufp->fullCData(oldp+35,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_i),5);
    bufp->fullCData(oldp+36,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_o),5);
    bufp->fullCData(oldp+37,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin),5);
    bufp->fullCData(oldp+38,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_sync__DOT__ptr_temp),5);
    bufp->fullBit(oldp+39,(vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.empty));
    bufp->fullBit(oldp+40,(vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__w_full));
    bufp->fullCData(oldp+41,((0x0000000fU & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin))),4);
    bufp->fullCData(oldp+42,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_i),5);
    bufp->fullCData(oldp+43,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_o),5);
    bufp->fullCData(oldp+44,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin),5);
    bufp->fullCData(oldp+45,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_sync__DOT__ptr_temp),5);
    bufp->fullBit(oldp+46,(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.full));
    bufp->fullCData(oldp+47,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_leaf_scope__Vstatic__bracket_match),8);
    bufp->fullIData(oldp+48,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_leaf_scope__Vstatic__pos),32);
    bufp->fullIData(oldp+49,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_leaf_scope__Vstatic__bmatches),32);
    bufp->fullBit(oldp+50,(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.clk));
    bufp->fullBit(oldp+51,(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.reset_n));
    bufp->fullBit(oldp+52,(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.clk));
    bufp->fullBit(oldp+53,(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.reset_n));
    bufp->fullCData(oldp+54,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data
                             [(0x0000000fU & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin))]),8);
    bufp->fullCData(oldp+55,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_gray_next),5);
    bufp->fullCData(oldp+56,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin_next),5);
    bufp->fullBit(oldp+57,(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_empty_tmp));
    bufp->fullIData(oldp+58,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_re_match__Vstatic__e),32);
    bufp->fullIData(oldp+59,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_re_match__Vstatic__es),32);
    bufp->fullIData(oldp+60,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_re_match__Vstatic__s),32);
    bufp->fullIData(oldp+61,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_re_match__Vstatic__ss),32);
    bufp->fullIData(oldp+62,(vlSymsp->TOP__uvm_pkg.__PVT__m_uvm_core_state),32);
    bufp->fullCData(oldp+63,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_instance_scope__Vstatic__c),8);
    bufp->fullIData(oldp+64,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_instance_scope__Vstatic__pos),32);
    bufp->fullBit(oldp+65,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_oneway_hash__Vstatic__msb));
    bufp->fullCData(oldp+66,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_oneway_hash__Vstatic__current_byte),8);
    bufp->fullIData(oldp+67,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_oneway_hash__Vstatic__crc1),32);
    bufp->fullIData(oldp+68,(vlSymsp->TOP__uvm_pkg.__PVT__uvm_wait_for_nba_region__Vstatic__next_nba),32);
    bufp->fullBit(oldp+69,(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.clk));
    bufp->fullBit(oldp+70,(vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.clk));
}
