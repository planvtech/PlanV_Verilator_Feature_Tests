// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TLM_FIFO_BASE__TZ353__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TLM_FIFO_BASE__TZ353__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_abstract_component_registry__pi251;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz353;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz353_TBz421;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_event;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz353;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz353__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz353__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz353__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz353__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_abstract_component_registry__pi251> &get_type__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_component__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz353 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_component {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz353_TBz421> __PVT__put_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421> __PVT__get_peek_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz353> __PVT__put_ap;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz353> __PVT__get_ap;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz353_TBz421> __PVT__blocking_put_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_put_imp__Tz353_TBz421> __PVT__nonblocking_put_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421> __PVT__blocking_get_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421> __PVT__nonblocking_get_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421> __PVT__get_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421> __PVT__blocking_peek_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421> __PVT__nonblocking_peek_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421> __PVT__peek_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421> __PVT__blocking_get_peek_export;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_peek_imp__Tz353_TBz421> __PVT__nonblocking_get_peek_export;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_can_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_get__Vfuncrtn);
    virtual void __VnoInFunc_can_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_peek__Vfuncrtn);
    virtual void __VnoInFunc_can_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_put__Vfuncrtn);
    virtual void __VnoInFunc_flush(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_is_empty(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_empty__Vfuncrtn);
    virtual void __VnoInFunc_is_full(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_full__Vfuncrtn);
    virtual void __VnoInFunc_ok_to_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_event> &ok_to_get__Vfuncrtn);
    virtual void __VnoInFunc_ok_to_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_event> &ok_to_peek__Vfuncrtn);
    virtual void __VnoInFunc_ok_to_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_event> &ok_to_put__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_peek(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    virtual VlCoroutine __VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &size__Vfuncrtn);
    virtual void __VnoInFunc_try_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t, CData/*0:0*/ &try_get__Vfuncrtn);
    virtual void __VnoInFunc_try_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t, CData/*0:0*/ &try_peek__Vfuncrtn);
    virtual void __VnoInFunc_try_put(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t, CData/*0:0*/ &try_put__Vfuncrtn);
    virtual void __VnoInFunc_use_automatic_config(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &use_automatic_config__Vfuncrtn);
    virtual void __VnoInFunc_used(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &used__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz353(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz353();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo_base__Tz353>& obj);

#endif  // guard
