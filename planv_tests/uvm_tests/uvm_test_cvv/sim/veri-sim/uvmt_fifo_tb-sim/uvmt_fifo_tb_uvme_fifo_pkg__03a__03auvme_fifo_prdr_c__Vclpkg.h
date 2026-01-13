// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03AUVME_FIFO_PRDR_C__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03AUVME_FIFO_PRDR_C__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz154;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz155;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi76;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_input__pi75;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c__Vclpkg();
    ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi76> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_component__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_component {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __Vtrigprevexpr_hb998f206__0;
    CData/*0:0*/ __Vtrigprevexpr_hb7c3d9d2__0;
    CData/*0:0*/ __Vtrigprevexpr_h15e9d615__0;
    CData/*0:0*/ __Vtrigprevexpr_hceeb07e9__0;
    IData/*31:0*/ __PVT__fifo_depth;
    VlQueue<CData/*7:0*/> __PVT__fifo;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c> __PVT__cfg;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c> __PVT__cntxt;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74> __PVT__wr_input_imp;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_input__pi75> __PVT__rd_input_imp;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz154> __PVT__wr_output_port;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz155> __PVT__rd_output_port;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c>> __PVT__wr_queue;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c>> __PVT__rd_queue;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_connect_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_process_read(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> tr);
    virtual VlCoroutine __VnoInFunc_process_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> tr);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_run_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
  private:
    VlCoroutine __VnoInFunc_run_phase____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> wr_tr, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk1__DOT____VforkParent);
    VlCoroutine __VnoInFunc_run_phase____Vfork_1__1(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> rd_tr, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk1__DOT____VforkParent);
  public:
    virtual void __VnoInFunc_write_rd_input(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> tr);
    virtual void __VnoInFunc_write_wr_input(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> tr);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c>& obj);

#endif  // guard
