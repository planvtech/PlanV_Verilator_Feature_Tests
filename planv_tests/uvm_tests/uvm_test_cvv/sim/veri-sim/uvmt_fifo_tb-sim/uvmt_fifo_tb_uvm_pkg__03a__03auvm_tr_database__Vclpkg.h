// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TR_DATABASE__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TR_DATABASE__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_link_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_is_opened;
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream>, CData/*0:0*/> __PVT__m_streams;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_close_db(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &close_db__Vfuncrtn);
    virtual void __VnoInFunc_do_close_db(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &do_close_db__Vfuncrtn);
    virtual void __VnoInFunc_do_establish_link(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_link_base> link);
    virtual void __VnoInFunc_do_open_db(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &do_open_db__Vfuncrtn);
    virtual void __VnoInFunc_do_open_stream(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, std::string scope, std::string type_name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream> &do_open_stream__Vfuncrtn);
    void __VnoInFunc_establish_link(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_link_base> link);
    void __VnoInFunc_get_streams(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream>> &q, CData/*0:0*/ &get_streams__Vfuncrtn);
    void __VnoInFunc_is_open(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_open__Vfuncrtn);
    void __VnoInFunc_m_free_stream(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream> stream);
    void __VnoInFunc_open_db(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &open_db__Vfuncrtn);
    void __VnoInFunc_open_stream(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, std::string scope, std::string type_name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream> &open_stream__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database>& obj);

#endif  // guard
