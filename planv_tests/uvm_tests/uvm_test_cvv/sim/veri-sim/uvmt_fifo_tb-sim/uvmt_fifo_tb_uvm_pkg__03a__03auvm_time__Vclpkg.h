// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TIME__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TIME__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_time__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    double __PVT__m_resolution;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_time__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_time__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_time__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_set_time_resolution(uvmt_fifo_tb__Syms* __restrict vlSymsp, double res);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_time : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    QData/*63:0*/ __PVT__m_time;
    double __PVT__m_res;
    std::string __PVT__m_name;
    void __VnoInFunc_decr(uvmt_fifo_tb__Syms* __restrict vlSymsp, double t, QData/*63:0*/ scaled, double secs);
    void __VnoInFunc_get_abstime(uvmt_fifo_tb__Syms* __restrict vlSymsp, double secs, double &get_abstime__Vfuncrtn);
    void __VnoInFunc_get_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_name__Vfuncrtn);
    void __VnoInFunc_get_realtime(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ scaled, double secs, double &get_realtime__Vfuncrtn);
    void __VnoInFunc_incr(uvmt_fifo_tb__Syms* __restrict vlSymsp, double t, QData/*63:0*/ scaled, double secs);
    void __VnoInFunc_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_set_abstime(uvmt_fifo_tb__Syms* __restrict vlSymsp, double t, double secs);
    void __VnoInFunc_to_m_res(uvmt_fifo_tb__Syms* __restrict vlSymsp, double t, QData/*63:0*/ scaled, double secs, double &to_m_res__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_time(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, double res);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_time() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_time>& obj);

#endif  // guard
