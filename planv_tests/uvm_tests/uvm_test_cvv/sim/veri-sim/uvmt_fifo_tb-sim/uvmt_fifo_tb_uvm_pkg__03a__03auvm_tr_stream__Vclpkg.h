// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TR_STREAM__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TR_STREAM__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_tr_stream_cfg;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_set_before_get_dap__Tz26;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream>, IData/*31:0*/> __PVT__m_ids_by_stream;
    VlAssocArray<IData/*31:0*/, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream>> __PVT__m_streams_by_id;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_stream_from_handle(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ id, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream> &get_stream_from_handle__Vfuncrtn);
    void __VnoInFunc_m_free_id(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ id);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_warn_null_cfg;
    CData/*0:0*/ __PVT__m_is_opened;
    CData/*0:0*/ __PVT__m_is_closed;
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder>, CData/*0:0*/> __PVT__m_records;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_set_before_get_dap__Tz26> __PVT__m_cfg_dap;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_close(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_do_close(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_do_free(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_do_open(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database> db, std::string scope, std::string stream_type_name);
    virtual void __VnoInFunc_do_open_recorder(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, QData/*63:0*/ open_time, std::string type_name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> &do_open_recorder__Vfuncrtn);
    void __VnoInFunc_free(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_get_db(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database> &get_db__Vfuncrtn);
    void __VnoInFunc_get_handle(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_handle__Vfuncrtn);
    void __VnoInFunc_get_recorders(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder>> &q, CData/*0:0*/ &get_recorders__Vfuncrtn);
    void __VnoInFunc_get_scope(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_scope__Vfuncrtn);
    void __VnoInFunc_get_stream_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_stream_type_name__Vfuncrtn);
    void __VnoInFunc_is_closed(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_closed__Vfuncrtn);
    void __VnoInFunc_is_open(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_open__Vfuncrtn);
    void __VnoInFunc_m_do_open(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database> db, std::string scope, std::string stream_type_name);
    void __VnoInFunc_m_free_recorder(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> recorder);
    void __VnoInFunc_open_recorder(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, QData/*63:0*/ open_time, std::string type_name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> &open_recorder__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream>& obj);

#endif  // guard
