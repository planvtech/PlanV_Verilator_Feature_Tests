// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REG_INDIRECT_FTDR_SEQ__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REG_INDIRECT_FTDR_SEQ__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__m_idx;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> __PVT__m_addr_reg;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> __PVT__m_data_reg;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_body(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> addr_reg, IData/*31:0*/ idx, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> data_reg);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_indirect_ftdr_seq>& obj);

#endif  // guard
