// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TRANSACTION__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TRANSACTION__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_event_;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_string_pool__Tz13;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_parent_child_link;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_transaction;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_transaction__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_transaction__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_transaction__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_transaction__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_transaction : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__m_transaction_id;
    QData/*63:0*/ __PVT__begin_time;
    QData/*63:0*/ __PVT__end_time;
    QData/*63:0*/ __PVT__accept_time;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_string_pool__Tz13> __PVT__events;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> __PVT__initiator;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream> __PVT__stream_handle;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> __PVT__tr_recorder;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_accept_tr(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ accept_time);
    void __VnoInFunc_begin_child_tr(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ begin_time, IData/*31:0*/ parent_handle, IData/*31:0*/ &begin_child_tr__Vfuncrtn);
    void __VnoInFunc_begin_tr(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ begin_time, IData/*31:0*/ &begin_tr__Vfuncrtn);
    void __VnoInFunc_disable_recording(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_do_accept_tr(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_do_begin_tr(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_do_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs);
    virtual void __VnoInFunc_do_end_tr(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual void __VnoInFunc_do_record(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> recorder);
    void __VnoInFunc_enable_recording(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream> stream);
    void __VnoInFunc_end_tr(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ end_time, CData/*0:0*/ free_handle);
    void __VnoInFunc_get_accept_time(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ &get_accept_time__Vfuncrtn);
    void __VnoInFunc_get_begin_time(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ &get_begin_time__Vfuncrtn);
    void __VnoInFunc_get_end_time(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ &get_end_time__Vfuncrtn);
    void __VnoInFunc_get_event_pool(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_string_pool__Tz13> &get_event_pool__Vfuncrtn);
    void __VnoInFunc_get_initiator(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> &get_initiator__Vfuncrtn);
    void __VnoInFunc_get_tr_handle(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_tr_handle__Vfuncrtn);
    void __VnoInFunc_get_transaction_id(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_transaction_id__Vfuncrtn);
    void __VnoInFunc_is_active(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_active__Vfuncrtn);
    void __VnoInFunc_is_recording_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_recording_enabled__Vfuncrtn);
    void __VnoInFunc_m_begin_tr(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ begin_time, IData/*31:0*/ parent_handle, IData/*31:0*/ &m_begin_tr__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    void __VnoInFunc_set_initiator(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> initiator);
    void __VnoInFunc_set_transaction_id(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ id);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_transaction(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> initiator);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_transaction();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_transaction>& obj);

#endif  // guard
