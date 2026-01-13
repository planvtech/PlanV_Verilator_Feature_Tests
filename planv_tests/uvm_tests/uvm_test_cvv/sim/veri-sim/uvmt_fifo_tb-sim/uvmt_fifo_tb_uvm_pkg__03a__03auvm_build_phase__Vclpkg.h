// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_BUILD_PHASE__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_BUILD_PHASE__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_topdown_phase;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase> __PVT__m_inst;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase> &get__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_topdown_phase__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_topdown_phase {
  public:
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_exec_func(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> comp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_build_phase>& obj);

#endif  // guard
