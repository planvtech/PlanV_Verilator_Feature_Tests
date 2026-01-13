// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SEQUENCER__TZ154_TBZ154__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SEQUENCER__TZ154_TBZ154__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__Tz231;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi122;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_request;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base__pi123;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_fifo__Tz154;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__Tz231> &get_type__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base__pi123__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base__pi123 {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__sequence_item_requested;
    CData/*0:0*/ __PVT__get_next_item_called;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi122> __PVT__seq_item_export;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t);
    virtual VlCoroutine __VnoInFunc_get_next_item(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_item_done(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> item);
    void __VnoInFunc_item_done_get_trigger_data(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &item_done_get_trigger_data__Vfuncrtn);
    void __VnoInFunc_item_done_trigger(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> item);
    virtual void __VnoInFunc_m_find_number_driver_connections(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &m_find_number_driver_connections__Vfuncrtn);
    VlCoroutine __VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t);
    virtual void __VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> t);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_stop_sequences(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_try_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> &t);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz154_TBz154>& obj);

#endif  // guard
