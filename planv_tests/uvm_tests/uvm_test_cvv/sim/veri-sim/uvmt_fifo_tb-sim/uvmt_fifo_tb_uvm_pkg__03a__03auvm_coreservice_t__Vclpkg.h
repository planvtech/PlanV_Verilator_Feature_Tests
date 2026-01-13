// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CORESERVICE_T__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CORESERVICE_T__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_copier;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_default_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_server;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_visitor_;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __PVT__inst;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> &get__Vfuncrtn);
    void __VnoInFunc_set(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> cs);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t : public virtual VlClass {
  public:
    virtual void __VnoInFunc_get_component_visitor(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_visitor_> &get_component_visitor__Vfuncrtn);
    virtual void __VnoInFunc_get_default_comparer(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer> &get_default_comparer__Vfuncrtn);
    virtual void __VnoInFunc_get_default_copier(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_copier> &get_default_copier__Vfuncrtn);
    virtual void __VnoInFunc_get_default_packer(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> &get_default_packer__Vfuncrtn);
    virtual void __VnoInFunc_get_default_printer(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> &get_default_printer__Vfuncrtn);
    virtual void __VnoInFunc_get_default_tr_database(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database> &get_default_tr_database__Vfuncrtn);
    virtual void __VnoInFunc_get_factory(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory> &get_factory__Vfuncrtn);
    virtual void __VnoInFunc_get_global_seed(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_global_seed__Vfuncrtn);
    virtual void __VnoInFunc_get_phase_max_ready_to_end(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_phase_max_ready_to_end__Vfuncrtn);
    virtual void __VnoInFunc_get_report_server(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_server> &get_report_server__Vfuncrtn);
    virtual void __VnoInFunc_get_resource_pool(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool> &get_resource_pool__Vfuncrtn);
    virtual void __VnoInFunc_get_resource_pool_default_precedence(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_resource_pool_default_precedence__Vfuncrtn);
    virtual void __VnoInFunc_get_root(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> &get_root__Vfuncrtn);
    virtual void __VnoInFunc_get_uvm_seeding(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &get_uvm_seeding__Vfuncrtn);
    virtual void __VnoInFunc_set_component_visitor(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_visitor_> v);
    virtual void __VnoInFunc_set_default_comparer(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer> comparer);
    virtual void __VnoInFunc_set_default_copier(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_copier> copier);
    virtual void __VnoInFunc_set_default_packer(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    virtual void __VnoInFunc_set_default_printer(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual void __VnoInFunc_set_default_tr_database(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database> db);
    virtual void __VnoInFunc_set_factory(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory> f);
    virtual void __VnoInFunc_set_phase_max_ready_to_end(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ max);
    virtual void __VnoInFunc_set_report_server(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_server> server);
    virtual void __VnoInFunc_set_resource_pool(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool> pool);
    virtual void __VnoInFunc_set_resource_pool_default_precedence(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ precedence);
    virtual void __VnoInFunc_set_uvm_seeding(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ enable);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t>& obj);

#endif  // guard
