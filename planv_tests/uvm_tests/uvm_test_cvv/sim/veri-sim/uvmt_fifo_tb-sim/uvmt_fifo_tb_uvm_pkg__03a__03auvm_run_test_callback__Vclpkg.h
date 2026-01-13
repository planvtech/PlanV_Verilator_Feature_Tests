// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_RUN_TEST_CALLBACK__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_RUN_TEST_CALLBACK__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback>> __PVT__m_registered_cbs;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_add(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback> cb, CData/*0:0*/ &add__Vfuncrtn);
    void __VnoInFunc_delete(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback> cb, CData/*0:0*/ &delete__Vfuncrtn);
    void __VnoInFunc_m_do_post_run_test(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_m_do_pre_abort(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_m_do_pre_run_test(uvmt_fifo_tb__Syms* __restrict vlSymsp);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback {
  public:
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_post_run_test(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_pre_abort(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_pre_run_test(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_run_test_callback>& obj);

#endif  // guard
