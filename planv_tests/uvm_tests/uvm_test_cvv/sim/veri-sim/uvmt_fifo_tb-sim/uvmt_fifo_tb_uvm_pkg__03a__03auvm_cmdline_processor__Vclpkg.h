// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CMDLINE_PROCESSOR__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CMDLINE_PROCESSOR__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor> __PVT__m_inst;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_inst(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor> &get_inst__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object {
  public:

    // DESIGN SPECIFIC STATE
    VlQueue<std::string> __PVT__m_argv;
    VlQueue<std::string> __PVT__m_plus_argv;
    VlQueue<std::string> __PVT__m_uvm_argv;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_get_arg_matches(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string match, VlQueue<std::string> &args, IData/*31:0*/ &get_arg_matches__Vfuncrtn);
    void __VnoInFunc_get_arg_value(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string match, std::string &value, IData/*31:0*/ &get_arg_value__Vfuncrtn);
    void __VnoInFunc_get_arg_values(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string match, VlQueue<std::string> &values, IData/*31:0*/ &get_arg_values__Vfuncrtn);
    void __VnoInFunc_get_args(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<std::string> &args);
    void __VnoInFunc_get_plusargs(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<std::string> &args);
    void __VnoInFunc_get_tool_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_tool_name__Vfuncrtn);
    void __VnoInFunc_get_tool_version(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_tool_version__Vfuncrtn);
    void __VnoInFunc_get_uvm_args(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<std::string> &args);
    void __VnoInFunc_m_convert_verb(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string verb_str, IData/*31:0*/ &verb_enum, CData/*0:0*/ &m_convert_verb__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_cmdline_processor>& obj);

#endif  // guard
