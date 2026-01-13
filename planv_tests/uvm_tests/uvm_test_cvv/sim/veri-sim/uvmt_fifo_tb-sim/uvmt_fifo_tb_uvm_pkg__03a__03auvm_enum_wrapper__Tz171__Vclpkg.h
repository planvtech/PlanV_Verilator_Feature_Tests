// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_ENUM_WRAPPER__TZ171__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_ENUM_WRAPPER__TZ171__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlAssocArray<std::string, CData/*0:0*/> __PVT__map;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_from_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, CData/*0:0*/ &value, CData/*0:0*/ &from_name__Vfuncrtn);
    void __VnoInFunc_m_init_map(uvmt_fifo_tb__Syms* __restrict vlSymsp);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171 : public virtual VlClass {
  public:
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_enum_wrapper__Tz171>& obj);

#endif  // guard
