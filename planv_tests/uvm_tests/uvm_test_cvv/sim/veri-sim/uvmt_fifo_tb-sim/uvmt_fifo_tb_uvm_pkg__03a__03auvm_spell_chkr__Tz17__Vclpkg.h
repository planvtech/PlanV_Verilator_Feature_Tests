// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SPELL_CHKR__TZ17__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SPELL_CHKR__TZ17__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_spell_chkr__Tz17__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__max;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_spell_chkr__Tz17__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_spell_chkr__Tz17__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_spell_chkr__Tz17__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_check(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8>> &strtab, std::string s, CData/*0:0*/ &check__Vfuncrtn);
    void __VnoInFunc_levenshtein_distance(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string s, std::string t, IData/*31:0*/ &levenshtein_distance__Vfuncrtn);
    void __VnoInFunc_minimum(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ a, IData/*31:0*/ b, IData/*31:0*/ c, IData/*31:0*/ &minimum__Vfuncrtn);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_spell_chkr__Tz17 : public virtual VlClass {
  public:
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_spell_chkr__Tz17(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_spell_chkr__Tz17() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_spell_chkr__Tz17>& obj);

#endif  // guard
