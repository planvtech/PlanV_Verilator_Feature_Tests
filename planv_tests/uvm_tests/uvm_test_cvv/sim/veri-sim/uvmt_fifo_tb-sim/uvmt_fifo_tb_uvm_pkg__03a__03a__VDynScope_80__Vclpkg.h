// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03A__VDYNSCOPE_80__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03A__VDYNSCOPE_80__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80 : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> __PVT__seq;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> __PVT__phase;
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80>& obj);

#endif  // guard
