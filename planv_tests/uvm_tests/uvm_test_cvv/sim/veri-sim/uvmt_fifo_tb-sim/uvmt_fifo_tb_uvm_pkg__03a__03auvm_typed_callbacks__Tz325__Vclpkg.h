// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TYPED_CALLBACKS__TZ325__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TYPED_CALLBACKS__TZ325__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz76_TBz77;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz55;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid_base;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    std::string __PVT__m_typename;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz55> __PVT__m_tw_cb_q;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325> __PVT__m_t_inst;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_display(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> obj);
    void __VnoInFunc_m_cb_find(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz55> q, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, IData/*31:0*/ &m_cb_find__Vfuncrtn);
    void __VnoInFunc_m_cb_find_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz55> q, std::string name, std::string where, IData/*31:0*/ &m_cb_find_name__Vfuncrtn);
    void __VnoInFunc_m_initialize(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325> &m_initialize__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base {
  public:
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_m_add_tw_cbs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, IData/*31:0*/ ordering);
    virtual void __VnoInFunc_m_am_i_a(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> obj, CData/*0:0*/ &m_am_i_a__Vfuncrtn);
    virtual void __VnoInFunc_m_delete_tw_cbs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, CData/*0:0*/ &m_delete_tw_cbs__Vfuncrtn);
    virtual void __VnoInFunc_m_get_tw_cb_q(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz55> &m_get_tw_cb_q__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz325>& obj);

#endif  // guard
