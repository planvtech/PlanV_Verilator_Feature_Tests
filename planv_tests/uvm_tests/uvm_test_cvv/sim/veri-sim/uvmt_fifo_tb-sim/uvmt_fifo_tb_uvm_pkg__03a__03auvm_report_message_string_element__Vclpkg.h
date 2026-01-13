// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REPORT_MESSAGE_STRING_ELEMENT__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REPORT_MESSAGE_STRING_ELEMENT__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_string_element;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_string_element__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_string_element__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_string_element__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_string_element__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_string_element : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base {
  public:

    // DESIGN SPECIFIC STATE
    std::string __PVT___val;
    virtual void __VnoInFunc_do_clone(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base> &do_clone__Vfuncrtn);
    virtual void __VnoInFunc_do_copy(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base> rhs);
    virtual void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual void __VnoInFunc_do_record(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> recorder);
    virtual void __VnoInFunc_get_value(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_value__Vfuncrtn);
    virtual void __VnoInFunc_set_value(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string value);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_string_element(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_string_element();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_string_element>& obj);

#endif  // guard
