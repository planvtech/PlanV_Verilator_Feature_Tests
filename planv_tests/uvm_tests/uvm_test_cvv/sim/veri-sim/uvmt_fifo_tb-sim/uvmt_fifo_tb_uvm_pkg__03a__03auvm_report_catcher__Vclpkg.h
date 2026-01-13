// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REPORT_CATCHER__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REPORT_CATCHER__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__Tz75_TBz319;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_catcher;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_handler;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_container;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_server;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_catcher__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_register_cb_uvm_report_catcher;
    CData/*0:0*/ __PVT__m_set_action_called;
    CData/*0:0*/ __PVT__do_report;
    CData/*0:0*/ __PVT__process_all_report_catchers__Vstatic__in_catcher;
    IData/*31:0*/ __PVT__m_demoted_fatal;
    IData/*31:0*/ __PVT__m_demoted_error;
    IData/*31:0*/ __PVT__m_demoted_warning;
    IData/*31:0*/ __PVT__m_caught_fatal;
    IData/*31:0*/ __PVT__m_caught_error;
    IData/*31:0*/ __PVT__m_caught_warning;
    IData/*31:0*/ __PVT__DO_NOT_CATCH;
    IData/*31:0*/ __PVT__DO_NOT_MODIFY;
    IData/*31:0*/ __PVT__m_debug_flags;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message> __PVT__m_modified_report_message;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message> __PVT__m_orig_report_message;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__Tz75_TBz319> __PVT__print_catcher__Vstatic__iter;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_catcher__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_catcher__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_catcher__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_debug_report_catcher(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ what);
    void __VnoInFunc_print_catcher(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ file);
    void __VnoInFunc_process_all_report_catchers(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message> rm, IData/*31:0*/ &process_all_report_catchers__Vfuncrtn);
    void __VnoInFunc_summarize(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_catcher : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback {
  public:
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_add_int(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlWide<128>/*4095:0*/ value, IData/*31:0*/ size, IData/*27:0*/ radix, IData/*31:0*/ action);
    void __VnoInFunc_add_object(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> obj, IData/*31:0*/ action);
    void __VnoInFunc_add_string(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, std::string value, IData/*31:0*/ action);
    virtual void __VnoInFunc_catch(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &catch__Vfuncrtn);
    void __VnoInFunc_get_action(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_action__Vfuncrtn);
    void __VnoInFunc_get_client(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object> &get_client__Vfuncrtn);
    void __VnoInFunc_get_context(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_context__Vfuncrtn);
    void __VnoInFunc_get_element_container(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_container> &get_element_container__Vfuncrtn);
    void __VnoInFunc_get_fname(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_fname__Vfuncrtn);
    void __VnoInFunc_get_id(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_id__Vfuncrtn);
    void __VnoInFunc_get_line(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_line__Vfuncrtn);
    void __VnoInFunc_get_message(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_message__Vfuncrtn);
    void __VnoInFunc_get_severity(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ &get_severity__Vfuncrtn);
    void __VnoInFunc_get_verbosity(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_verbosity__Vfuncrtn);
    void __VnoInFunc_issue(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_process_report_catcher(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &process_report_catcher__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    void __VnoInFunc_set_action(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ action);
    void __VnoInFunc_set_context(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string context_str);
    void __VnoInFunc_set_id(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string id);
    void __VnoInFunc_set_message(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string message);
    void __VnoInFunc_set_severity(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity);
    void __VnoInFunc_set_verbosity(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ verbosity);
    void __VnoInFunc_uvm_process_report_message(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message> msg);
    void __VnoInFunc_uvm_report(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*1:0*/ severity, std::string id, std::string message, IData/*31:0*/ verbosity, std::string fname, IData/*31:0*/ line, std::string context_name, CData/*0:0*/ report_enabled_checked);
    void __VnoInFunc_uvm_report_error(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string id, std::string message, IData/*31:0*/ verbosity, std::string fname, IData/*31:0*/ line, std::string context_name, CData/*0:0*/ report_enabled_checked);
    void __VnoInFunc_uvm_report_fatal(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string id, std::string message, IData/*31:0*/ verbosity, std::string fname, IData/*31:0*/ line, std::string context_name, CData/*0:0*/ report_enabled_checked);
    void __VnoInFunc_uvm_report_info(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string id, std::string message, IData/*31:0*/ verbosity, std::string fname, IData/*31:0*/ line, std::string context_name, CData/*0:0*/ report_enabled_checked);
    void __VnoInFunc_uvm_report_warning(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string id, std::string message, IData/*31:0*/ verbosity, std::string fname, IData/*31:0*/ line, std::string context_name, CData/*0:0*/ report_enabled_checked);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_catcher(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_catcher();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_catcher>& obj);

#endif  // guard
