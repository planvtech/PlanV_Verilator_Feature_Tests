// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CALLBACK_ITER__PI191__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CALLBACK_ITER__PI191__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_cbs;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi191__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi191__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi191__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi191__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi191 : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__m_i;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg> __PVT__m_obj;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_cbs> __PVT__m_cb;
    void __VnoInFunc_first(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_cbs> &first__Vfuncrtn);
    void __VnoInFunc_get_cb(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_cbs> &get_cb__Vfuncrtn);
    void __VnoInFunc_last(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_cbs> &last__Vfuncrtn);
    void __VnoInFunc_next(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_cbs> &next__Vfuncrtn);
    void __VnoInFunc_prev(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_cbs> &prev__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi191(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg> obj);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi191() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi191>& obj);

#endif  // guard
