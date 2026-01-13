// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03A__VDYNSCOPE_71__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03A__VDYNSCOPE_71__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71 : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__triggered;
    QData/*63:0*/ __PVT__last_trigger;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __PVT__obj;
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71>& obj);

#endif  // guard
