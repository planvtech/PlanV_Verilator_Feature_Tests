// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TLM_FIFO__TZ34__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TLM_FIFO__TZ34__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03amailbox__Tz34;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz34;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__Tz280;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz34;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz34__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz34__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz34__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz34__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__Tz280> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz34__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz34 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz34 {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__m_size;
    IData/*31:0*/ __PVT__m_pending_blocked_gets;
    VlClassRef<uvmt_fifo_tb_std__03a__03amailbox__Tz34> __PVT__m;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_can_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_get__Vfuncrtn);
    virtual void __VnoInFunc_can_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_peek__Vfuncrtn);
    virtual void __VnoInFunc_can_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_put__Vfuncrtn);
    virtual void __VnoInFunc_flush(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_is_empty(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_empty__Vfuncrtn);
    virtual void __VnoInFunc_is_full(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_full__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t);
    virtual VlCoroutine __VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &size__Vfuncrtn);
    virtual void __VnoInFunc_try_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t, CData/*0:0*/ &try_get__Vfuncrtn);
    virtual void __VnoInFunc_try_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t, CData/*0:0*/ &try_peek__Vfuncrtn);
    virtual void __VnoInFunc_try_put(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t, CData/*0:0*/ &try_put__Vfuncrtn);
    virtual void __VnoInFunc_used(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &used__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz34(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent, IData/*31:0*/ size);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz34();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz34>& obj);

#endif  // guard
