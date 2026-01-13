// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TLM_IF_BASE__TZ353_TBZ353__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TLM_IF_BASE__TZ353_TBZ353__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_if_base__Tz353_TBz353__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_if_base__Tz353_TBz353__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_if_base__Tz353_TBz353__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_if_base__Tz353_TBz353__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_if_base__Tz353_TBz353 : public virtual VlClass {
  public:
    virtual void __VnoInFunc_can_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_get__Vfuncrtn);
    virtual void __VnoInFunc_can_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_peek__Vfuncrtn);
    virtual void __VnoInFunc_can_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &can_put__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    virtual void __VnoInFunc_nb_transport(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> req, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &rsp, CData/*0:0*/ &nb_transport__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t);
    virtual VlCoroutine __VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t);
    virtual void __VnoInFunc_transport(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> req, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &rsp);
    virtual void __VnoInFunc_try_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t, CData/*0:0*/ &try_get__Vfuncrtn);
    virtual void __VnoInFunc_try_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> &t, CData/*0:0*/ &try_peek__Vfuncrtn);
    virtual void __VnoInFunc_try_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t, CData/*0:0*/ &try_put__Vfuncrtn);
    virtual void __VnoInFunc_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> t);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_if_base__Tz353_TBz353(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_if_base__Tz353_TBz353();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_if_base__Tz353_TBz353>& obj);

#endif  // guard
