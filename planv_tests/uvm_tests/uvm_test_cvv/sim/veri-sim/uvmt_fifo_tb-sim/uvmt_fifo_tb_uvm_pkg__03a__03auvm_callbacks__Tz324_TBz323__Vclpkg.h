// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CALLBACKS__TZ324_TBZ323__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CALLBACKS__TZ324_TBZ323__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz76_TBz77;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz55;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_cbs;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz324;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz323;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz324;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid__Tz55;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid_base;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    std::string __PVT__m_typename;
    std::string __PVT__m_cb_typename;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323> __PVT__m_inst;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid_base> __PVT__m_typeid;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_typeid_base> __PVT__m_cb_typeid;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324> __PVT__m_base_inst;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_add(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, IData/*31:0*/ ordering);
    void __VnoInFunc_add_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> root, IData/*31:0*/ ordering);
    void __VnoInFunc_delete(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb);
    void __VnoInFunc_delete_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> root);
    void __VnoInFunc_display(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> obj);
    void __VnoInFunc_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323> &get__Vfuncrtn);
    void __VnoInFunc_get_all(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_cbs>> &all_callbacks, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> obj);
    void __VnoInFunc_get_first(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &itr, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_cbs> &get_first__Vfuncrtn);
    void __VnoInFunc_get_last(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &itr, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_cbs> &get_last__Vfuncrtn);
    void __VnoInFunc_get_next(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &itr, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_cbs> &get_next__Vfuncrtn);
    void __VnoInFunc_get_prev(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &itr, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_cbs> &get_prev__Vfuncrtn);
    void __VnoInFunc_m_get_q(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz55> &q, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> obj);
    void __VnoInFunc_m_register_pair(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string tname, std::string cbname, CData/*0:0*/ &m_register_pair__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz324__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_typed_callbacks__Tz324 {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_registered;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_m_is_for_me(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, CData/*0:0*/ &m_is_for_me__Vfuncrtn);
    virtual void __VnoInFunc_m_is_registered(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> obj, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback> cb, CData/*0:0*/ &m_is_registered__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callbacks__Tz324_TBz323>& obj);

#endif  // guard
