// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_EVENT___VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_EVENT___VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_event__Tz5;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_callback_;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz13;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_event___Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_cb_registered;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_event___Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_event___Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_event___Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz13> &get_type__Vfuncrtn);
    void __VnoInFunc_m_register_cb(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &m_register_cb__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_base__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_ : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_base {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __PVT__trigger_data;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __PVT__default_data;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn);
    virtual void __VnoInFunc_do_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs);
    virtual void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual void __VnoInFunc_get_default_data(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &get_default_data__Vfuncrtn);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_trigger_data(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &get_trigger_data__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_set_default_data(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> data);
    virtual void __VnoInFunc_trigger(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> data);
    virtual void __VnoInFunc_trigger__Vtcwrap_1(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_wait_ptrigger_data(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &data);
    virtual VlCoroutine __VnoInFunc_wait_trigger_data(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &data);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_>& obj);

#endif  // guard
