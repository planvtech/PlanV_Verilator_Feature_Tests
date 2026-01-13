// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_PORT_COMPONENT__TZ266__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_PORT_COMPONENT__TZ266__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz266__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz266__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz266__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz266__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz266 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232> __PVT__m_port;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_get_connected_to(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base>> &list);
    void __VnoInFunc_get_port(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232> &get_port__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    void __VnoInFunc_is_export(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_export__Vfuncrtn);
    void __VnoInFunc_is_imp(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_imp__Vfuncrtn);
    void __VnoInFunc_is_port(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_port__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_resolve_bindings(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz266(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz232> port);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz266();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz266>& obj);

#endif  // guard
