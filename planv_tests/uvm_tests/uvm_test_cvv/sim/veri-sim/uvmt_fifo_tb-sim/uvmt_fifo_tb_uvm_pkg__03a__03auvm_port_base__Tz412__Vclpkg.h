// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_PORT_BASE__TZ412__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_PORT_BASE__TZ412__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz416;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    std::string __PVT__debug_connected_to__Vstatic__indent;
    std::string __PVT__debug_connected_to__Vstatic__save;
    std::string __PVT__debug_provided_to__Vstatic__indent;
    std::string __PVT__debug_provided_to__Vstatic__save;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_sqr_if_base__Tz353_TBz353 {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_resolved;
    IData/*31:0*/ __PVT__m_if_mask;
    IData/*31:0*/ __PVT__m_def_index;
    IData/*31:0*/ __PVT__m_port_type;
    IData/*31:0*/ __PVT__m_min_size;
    IData/*31:0*/ __PVT__m_max_size;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412> __PVT__m_if;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component__Tz416> __PVT__m_comp;
    VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412>> __PVT__m_provided_by;
    VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412>> __PVT__m_provided_to;
    VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412>> __PVT__m_imp_list;
    virtual void __VnoInFunc_connect(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412> provider);
    void __VnoInFunc_debug_connected_to(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ level, IData/*31:0*/ max_level);
    void __VnoInFunc_debug_provided_to(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ level, IData/*31:0*/ max_level);
    virtual void __VnoInFunc_get_comp(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_component_base> &get_comp__Vfuncrtn);
    void __VnoInFunc_get_connected_to(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412>> &list);
    virtual void __VnoInFunc_get_full_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_full_name__Vfuncrtn);
    void __VnoInFunc_get_if(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ index, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412> &get_if__Vfuncrtn);
    void __VnoInFunc_get_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_name__Vfuncrtn);
    virtual void __VnoInFunc_get_parent(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> &get_parent__Vfuncrtn);
    void __VnoInFunc_get_provided_to(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412>> &list);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    void __VnoInFunc_is_export(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_export__Vfuncrtn);
    void __VnoInFunc_is_imp(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_imp__Vfuncrtn);
    void __VnoInFunc_is_port(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_port__Vfuncrtn);
    void __VnoInFunc_is_unbounded(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_unbounded__Vfuncrtn);
    void __VnoInFunc_m_add_list(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412> provider);
    void __VnoInFunc_m_check_relationship(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412> provider, CData/*0:0*/ &m_check_relationship__Vfuncrtn);
    void __VnoInFunc_m_get_if_mask(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &m_get_if_mask__Vfuncrtn);
    void __VnoInFunc_max_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &max_size__Vfuncrtn);
    void __VnoInFunc_min_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &min_size__Vfuncrtn);
    virtual void __VnoInFunc_resolve_bindings(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_set_default_index(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ index);
    void __VnoInFunc_set_if(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ index);
    void __VnoInFunc_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &size__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent, IData/*31:0*/ port_type, IData/*31:0*/ min_size, IData/*31:0*/ max_size);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz412>& obj);

#endif  // guard
