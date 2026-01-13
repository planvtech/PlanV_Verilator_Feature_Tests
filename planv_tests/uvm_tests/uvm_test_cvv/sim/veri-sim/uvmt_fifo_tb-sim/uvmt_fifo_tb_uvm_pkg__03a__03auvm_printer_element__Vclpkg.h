// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_PRINTER_ELEMENT__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_PRINTER_ELEMENT__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    std::string __PVT__m_name;
    std::string __PVT__m_type_name;
    std::string __PVT__m_size;
    std::string __PVT__m_value;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element>> __PVT__m_children;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_add_child(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element> child);
    void __VnoInFunc_clear_children(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_get_children(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element>> &children, CData/*0:0*/ recurse);
    virtual void __VnoInFunc_get_element_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_element_name__Vfuncrtn);
    virtual void __VnoInFunc_get_element_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_element_size__Vfuncrtn);
    virtual void __VnoInFunc_get_element_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_element_type_name__Vfuncrtn);
    virtual void __VnoInFunc_get_element_value(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_element_value__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_set(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string element_name, std::string element_type_name, std::string element_size, std::string element_value);
    virtual void __VnoInFunc_set_element_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string element_name);
    virtual void __VnoInFunc_set_element_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string element_size);
    virtual void __VnoInFunc_set_element_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string element_type_name);
    virtual void __VnoInFunc_set_element_value(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string element_value);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer_element>& obj);

#endif  // guard
