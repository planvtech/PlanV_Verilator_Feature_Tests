// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SEQ_ITEM_PULL_IMP__PI244__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SEQ_ITEM_PULL_IMP__PI244__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz353_TBz353;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi244__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi244__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi244__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi244__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi244 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412 {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz353_TBz353> __PVT__m_imp;
    void __VnoInFunc_disable_auto_item_recording(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    VlCoroutine __VnoInFunc_get_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    void __VnoInFunc_has_do_available(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &has_do_available__Vfuncrtn);
    void __VnoInFunc_is_auto_item_recording_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_auto_item_recording_enabled__Vfuncrtn);
    void __VnoInFunc_item_done(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t);
    VlCoroutine __VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    void __VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t);
    void __VnoInFunc_put_response(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t);
    VlCoroutine __VnoInFunc_try_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    VlCoroutine __VnoInFunc_wait_for_sequences(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi244(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer__Tz353_TBz353> imp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi244();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi244>& obj);

#endif  // guard
