// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_STD__03A__03AMAILBOX__TZ34__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_STD__03A__03AMAILBOX__TZ34__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_std__03a__03amailbox__Tz34__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_std__03a__03amailbox__Tz34__Vclpkg();
    ~uvmt_fifo_tb_std__03a__03amailbox__Tz34__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_std__03a__03amailbox__Tz34__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_std__03a__03amailbox__Tz34 : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __Vtrigprevexpr_he535c10d__0;
    CData/*0:0*/ __Vtrigprevexpr_h235bea2c__0;
    CData/*0:0*/ __Vtrigprevexpr_h235bea2c__1;
    IData/*31:0*/ __PVT__m_bound;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item>> __PVT__m_queue;
    VlCoroutine __VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &message);
    void __VnoInFunc_num(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &num__Vfuncrtn);
    VlCoroutine __VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &message);
    VlCoroutine __VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> message);
    void __VnoInFunc_try_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &message, IData/*31:0*/ &try_get__Vfuncrtn);
    void __VnoInFunc_try_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &message, IData/*31:0*/ &try_peek__Vfuncrtn);
    void __VnoInFunc_try_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> message, IData/*31:0*/ &try_put__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_std__03a__03amailbox__Tz34(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ bound);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_std__03a__03amailbox__Tz34() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_std__03a__03amailbox__Tz34>& obj);

#endif  // guard
