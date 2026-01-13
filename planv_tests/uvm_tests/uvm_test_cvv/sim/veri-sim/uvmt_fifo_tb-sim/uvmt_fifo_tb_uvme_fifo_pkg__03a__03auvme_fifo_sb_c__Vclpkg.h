// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03AUVME_FIFO_SB_C__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03AUVME_FIFO_SB_C__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi81;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_scoreboard;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_act__pi78;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_exp__pi80;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_act__pi77;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c__Vclpkg();
    ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi81> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_scoreboard__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_scoreboard {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __Vtrigprevexpr_he351bd2e__0;
    CData/*0:0*/ __Vtrigprevexpr_h785d1aca__0;
    CData/*0:0*/ __Vtrigprevexpr_hdd71547c__0;
    CData/*0:0*/ __Vtrigprevexpr_h87517d80__0;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c> __PVT__cntxt;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c> __PVT__cfg;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c>> __PVT__wr_act_queue;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c>> __PVT__rd_act_queue;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c>> __PVT__wr_exp_queue;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c>> __PVT__rd_exp_queue;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_act__pi77> __PVT__wr_act_imp;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_act__pi78> __PVT__rd_act_imp;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79> __PVT__wr_exp_imp;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_exp__pi80> __PVT__rd_exp_imp;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_assign_cfg(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_assign_cntxt(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_create_sub_scoreboards(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_process_read(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_process_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_run_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
  private:
    VlCoroutine __VnoInFunc_run_phase____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk2__DOT____VforkParent);
    VlCoroutine __VnoInFunc_run_phase____Vfork_1__1(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk2__DOT____VforkParent);
  public:
    virtual void __VnoInFunc_write_rd_act(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> tr);
    virtual void __VnoInFunc_write_rd_exp(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_seq_item_c> tr);
    virtual void __VnoInFunc_write_wr_act(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> tr);
    virtual void __VnoInFunc_write_wr_exp(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> tr);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c>& obj);

#endif  // guard
