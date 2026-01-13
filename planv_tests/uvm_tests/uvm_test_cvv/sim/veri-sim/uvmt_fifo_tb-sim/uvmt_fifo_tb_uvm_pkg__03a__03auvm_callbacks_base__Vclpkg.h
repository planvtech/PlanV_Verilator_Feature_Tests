// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CALLBACKS_BASE__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CALLBACKS_BASE__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz76_TBz77;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz55;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid_base;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_tracing;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base> __PVT__m_b_inst;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz76_TBz77> __PVT__m_pool;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_m_initialize(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base> &m_initialize__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base>> __PVT__m_this_type;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid_base> __PVT__m_super_type;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid_base>> __PVT__m_derived_types;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_check_registration(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, CData/*0:0*/ &check_registration__Vfuncrtn);
    virtual void __VnoInFunc_m_add_tw_cbs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, IData/*31:0*/ ordering);
    virtual void __VnoInFunc_m_am_i_a(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> obj, CData/*0:0*/ &m_am_i_a__Vfuncrtn);
    virtual void __VnoInFunc_m_delete_tw_cbs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, CData/*0:0*/ &m_delete_tw_cbs__Vfuncrtn);
    virtual void __VnoInFunc_m_get_tw_cb_q(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz55> &m_get_tw_cb_q__Vfuncrtn);
    virtual void __VnoInFunc_m_is_for_me(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, CData/*0:0*/ &m_is_for_me__Vfuncrtn);
    virtual void __VnoInFunc_m_is_registered(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, CData/*0:0*/ &m_is_registered__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base>& obj);

#endif  // guard
