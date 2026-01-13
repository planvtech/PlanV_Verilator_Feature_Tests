// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"
VlAssocArray<IData/*31:0*/, CData/*0:0*/> uvmt_fifo_tb___024unit::__Venumtab_enum_valid25;
VlAssocArray<IData/*31:0*/, std::string> uvmt_fifo_tb___024unit::__Venumtab_enum_name37;
VlAssocArray<IData/*27:0*/, std::string> uvmt_fifo_tb___024unit::__Venumtab_enum_name15;
VlAssocArray<IData/*31:0*/, std::string> uvmt_fifo_tb___024unit::__Venumtab_enum_name25;
VlAssocArray<IData/*31:0*/, std::string> uvmt_fifo_tb___024unit::__Venumtab_enum_name75;
VlUnpacked<CData/*1:0*/, 4> uvmt_fifo_tb___024unit::__Venumtab_enum_next21;
VlUnpacked<std::string, 8> uvmt_fifo_tb___024unit::__Venumtab_enum_name35;
VlUnpacked<std::string, 2> uvmt_fifo_tb___024unit::__Venumtab_enum_name19;
VlUnpacked<std::string, 2> uvmt_fifo_tb___024unit::__Venumtab_enum_name115;
VlUnpacked<std::string, 4> uvmt_fifo_tb___024unit::__Venumtab_enum_name21;
VlUnpacked<std::string, 2> uvmt_fifo_tb___024unit::__Venumtab_enum_name71;
VlUnpacked<std::string, 4> uvmt_fifo_tb___024unit::__Venumtab_enum_name73;
VlUnpacked<std::string, 4> uvmt_fifo_tb___024unit::__Venumtab_enum_name93;
VlUnpacked<std::string, 4> uvmt_fifo_tb___024unit::__Venumtab_enum_name91;
VlUnpacked<std::string, 4> uvmt_fifo_tb___024unit::__Venumtab_enum_name85;
VlUnpacked<std::string, 4> uvmt_fifo_tb___024unit::__Venumtab_enum_name83;
VlUnpacked<std::string, 8> uvmt_fifo_tb___024unit::__Venumtab_enum_name89;
VlUnpacked<IData/*31:0*/, 4> uvmt_fifo_tb___024unit::__Venumvaltab_0;
VlUnpacked<IData/*31:0*/, 8> uvmt_fifo_tb___024unit::__Venumvaltab_1;
VlUnpacked<IData/*31:0*/, 5> uvmt_fifo_tb___024unit::__Venumvaltab_2;

void uvmt_fifo_tb___024unit___ctor_var_reset(uvmt_fifo_tb___024unit* vlSelf);

uvmt_fifo_tb___024unit::uvmt_fifo_tb___024unit() = default;
uvmt_fifo_tb___024unit::~uvmt_fifo_tb___024unit() = default;

void uvmt_fifo_tb___024unit::ctor(uvmt_fifo_tb__Syms* symsp, const char* namep) {
    vlSymsp = symsp;
    vlNamep = strdup(Verilated::catName(vlSymsp->name(), namep));
    // Reset structure values
    uvmt_fifo_tb___024unit___ctor_var_reset(this);
}

void uvmt_fifo_tb___024unit::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

void uvmt_fifo_tb___024unit::dtor() {
    VL_DO_DANGLING(std::free(const_cast<char*>(vlNamep)), vlNamep);
}
