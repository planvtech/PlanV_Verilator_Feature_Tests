// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REPORT_HANDLER__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REPORT_HANDLER__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi5;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz31_TBz31;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz30;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_server;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_format_action(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ action, std::string &format_action__Vfuncrtn);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi5> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__m_max_verbosity_level;
    IData/*31:0*/ __PVT__default_file_handle;
    VlAssocArray<CData/*1:0*/, IData/*31:0*/> __PVT__severity_actions;
    VlAssocArray<CData/*1:0*/, IData/*31:0*/> __PVT__severity_file_handles;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz30> __PVT__id_verbosities;
    VlAssocArray<CData/*1:0*/, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz30>> __PVT__severity_id_verbosities;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz30> __PVT__id_actions;
    VlAssocArray<CData/*1:0*/, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz30>> __PVT__severity_id_actions;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz31_TBz31> __PVT__sev_overrides;
    VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz31_TBz31>> __PVT__sev_id_overrides;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz30> __PVT__id_file_handles;
    VlAssocArray<CData/*1:0*/, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz30>> __PVT__severity_id_file_handles;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn);
    virtual void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    void __VnoInFunc_get_action(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, std::string id, IData/*31:0*/ &get_action__Vfuncrtn);
    void __VnoInFunc_get_file_handle(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, std::string id, IData/*31:0*/ &get_file_handle__Vfuncrtn);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    void __VnoInFunc_get_severity_id_file(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, std::string id, IData/*31:0*/ &get_severity_id_file__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    void __VnoInFunc_get_verbosity_level(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, std::string id, IData/*31:0*/ &get_verbosity_level__Vfuncrtn);
    void __VnoInFunc_initialize(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_process_report_message(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message> report_message);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_report(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, std::string name, std::string id, std::string message, IData/*31:0*/ verbosity_level, std::string filename, IData/*31:0*/ line, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object> client);
    void __VnoInFunc_set_default_file(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ file);
    void __VnoInFunc_set_id_action(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string id, IData/*31:0*/ action);
    void __VnoInFunc_set_id_file(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string id, IData/*31:0*/ file);
    void __VnoInFunc_set_id_verbosity(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string id, IData/*31:0*/ verbosity);
    void __VnoInFunc_set_severity_action(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, IData/*31:0*/ action);
    void __VnoInFunc_set_severity_file(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, IData/*31:0*/ file);
    void __VnoInFunc_set_severity_id_action(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, std::string id, IData/*31:0*/ action);
    void __VnoInFunc_set_severity_id_file(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, std::string id, IData/*31:0*/ file);
    void __VnoInFunc_set_severity_id_override(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ cur_severity, std::string id, CData/*1:0*/ new_severity);
    void __VnoInFunc_set_severity_id_verbosity(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, std::string id, IData/*31:0*/ verbosity);
    void __VnoInFunc_set_severity_override(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ cur_severity, CData/*1:0*/ new_severity);
    void __VnoInFunc_set_verbosity_level(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ verbosity_level);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler>& obj);

#endif  // guard
