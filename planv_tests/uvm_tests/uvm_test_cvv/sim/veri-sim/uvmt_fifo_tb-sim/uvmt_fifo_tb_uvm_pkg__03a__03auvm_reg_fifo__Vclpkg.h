// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REG_FIFO__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_REG_FIFO__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_field;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_fifo;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_fifo__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_fifo__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_fifo__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_fifo__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_fifo : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__m_set_cnt;
    IData/*31:0*/ __PVT__m_size;
    IData/*31:0*/ __Vfifo_size;
    VlQueue<QData/*63:0*/> __PVT__fifo;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_field> __PVT__value;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vresize_constrained_arrays(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_build(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_capacity(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &capacity__Vfuncrtn);
    virtual void __VnoInFunc_do_predict(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw, IData/*31:0*/ kind, CData/*7:0*/ be);
    virtual void __VnoInFunc_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string fname, IData/*31:0*/ lineno, QData/*63:0*/ &get__Vfuncrtn);
    void __VnoInFunc_post_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_pre_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    virtual void __VnoInFunc_pre_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_set(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ value, std::string fname, IData/*31:0*/ lineno);
    void __VnoInFunc_set_compare(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ check);
    void __VnoInFunc_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &size__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_update(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    void __VnoInFunc_valid_fifo_size_resize_constrained_array(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_valid_fifo_size_setup_constraint(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_fifo(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, IData/*31:0*/ size, IData/*31:0*/ n_bits, IData/*31:0*/ has_cover);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_fifo();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_fifo>& obj);

#endif  // guard
