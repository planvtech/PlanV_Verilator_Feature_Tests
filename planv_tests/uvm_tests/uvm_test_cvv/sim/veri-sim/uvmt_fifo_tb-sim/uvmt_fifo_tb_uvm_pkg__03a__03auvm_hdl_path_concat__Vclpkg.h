// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_HDL_PATH_CONCAT__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_HDL_PATH_CONCAT__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
#include "uvmt_fifo_tb_uvm_pkg.h"


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    VlQueue<uvmt_fifo_tb_uvm_hdl_path_slice__struct__0> __PVT__slices;
    void __VnoInFunc_add_path(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string path, IData/*31:0*/ offset, IData/*31:0*/ size);
    void __VnoInFunc_add_slice(uvmt_fifo_tb__Syms* __restrict vlSymsp, uvmt_fifo_tb_uvm_hdl_path_slice__struct__0 slice);
    void __VnoInFunc_set(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<uvmt_fifo_tb_uvm_hdl_path_slice__struct__0> t);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat>& obj);

#endif  // guard
