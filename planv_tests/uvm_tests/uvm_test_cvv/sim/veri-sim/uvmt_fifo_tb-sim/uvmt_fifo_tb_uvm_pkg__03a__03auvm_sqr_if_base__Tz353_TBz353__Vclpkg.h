// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SQR_IF_BASE__TZ353_TBZ353__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SQR_IF_BASE__TZ353_TBZ353__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353 : public virtual VlClass {
  public:
    virtual void __VnoInFunc_disable_auto_item_recording(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    virtual VlCoroutine __VnoInFunc_get_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    virtual void __VnoInFunc_has_do_available(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &has_do_available__Vfuncrtn);
    virtual void __VnoInFunc_is_auto_item_recording_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_auto_item_recording_enabled__Vfuncrtn);
    virtual void __VnoInFunc_item_done(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t);
    virtual VlCoroutine __VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    virtual void __VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t);
    virtual void __VnoInFunc_put_response(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t);
    virtual VlCoroutine __VnoInFunc_try_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    virtual VlCoroutine __VnoInFunc_wait_for_sequences(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353>& obj);

#endif  // guard
