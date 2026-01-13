// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_HEARTBEAT__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_HEARTBEAT__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat_callback;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_objection;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_started;
    CData/*0:0*/ __PVT__m_added;
    CData/*0:0*/ __Vtrigprevexpr_h83d8d36e__0;
    IData/*31:0*/ __PVT__m_mode;
    VlAssignableEvent __PVT__m_stop_event;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_objection> __PVT__m_objection;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat_callback> __PVT__m_cb;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> __PVT__m_cntxt;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component>> __PVT__m_hblist;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_> __PVT__m_event;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_add(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> comp);
    void __VnoInFunc_m_disable_cb(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_m_enable_cb(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_m_hb_process(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    VlCoroutine __VnoInFunc_m_hb_process____Vfork_2__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_71> __VDynScope_m_hb_process_2, VlForkSync __Vfork_2__sync);
    VlCoroutine __VnoInFunc_m_hb_process____Vfork_2__1(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlForkSync __Vfork_2__sync);
  public:
    void __VnoInFunc_m_start_hb_process(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    VlCoroutine __VnoInFunc_m_start_hb_process____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk2__DOT____VforkParent);
  public:
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    void __VnoInFunc_remove(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> comp);
    void __VnoInFunc_set_heartbeat(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_> e, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component>> &comps);
    void __VnoInFunc_set_mode(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ mode, IData/*31:0*/ &set_mode__Vfuncrtn);
    void __VnoInFunc_start(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_> e);
    void __VnoInFunc_stop(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> cntxt, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_objection> objection);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_heartbeat>& obj);

#endif  // guard
