// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_MEM_REGION__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_MEM_REGION__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__len;
    IData/*31:0*/ __PVT__n_bytes;
    IData/*31:0*/ __PVT__lineno;
    QData/*63:0*/ __PVT__Xstart_offsetX;
    QData/*63:0*/ __PVT__Xend_offsetX;
    std::string __PVT__fname;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam> __PVT__parent;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg> __PVT__XvregX;
    VlCoroutine __VnoInFunc_burst_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, VlQueue<QData/*63:0*/> &value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    VlCoroutine __VnoInFunc_burst_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, VlQueue<QData/*63:0*/> value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    void __VnoInFunc_convert2string(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &convert2string__Vfuncrtn);
    void __VnoInFunc_get_end_offset(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ &get_end_offset__Vfuncrtn);
    void __VnoInFunc_get_len(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_len__Vfuncrtn);
    void __VnoInFunc_get_memory(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> &get_memory__Vfuncrtn);
    void __VnoInFunc_get_n_bytes(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_n_bytes__Vfuncrtn);
    void __VnoInFunc_get_start_offset(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ &get_start_offset__Vfuncrtn);
    void __VnoInFunc_get_virtual_registers(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg> &get_virtual_registers__Vfuncrtn);
    void __VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ &value, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    void __VnoInFunc_poke(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ value, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    VlCoroutine __VnoInFunc_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ &value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    void __VnoInFunc_release_region(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ start_offset, QData/*63:0*/ end_offset, IData/*31:0*/ len, IData/*31:0*/ n_bytes, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam> parent);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region>& obj);

#endif  // guard
