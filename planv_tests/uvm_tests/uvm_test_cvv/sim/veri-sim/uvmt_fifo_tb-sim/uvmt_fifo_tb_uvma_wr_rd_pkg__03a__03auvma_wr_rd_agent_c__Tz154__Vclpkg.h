// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVMA_WR_RD_PKG__03A__03AUVMA_WR_RD_AGENT_C__TZ154__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVMA_WR_RD_PKG__03A__03AUVMA_WR_RD_AGENT_C__TZ154__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_agent;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz154;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi87;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi122;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_port__pi141;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_drv_c__Tz154;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz154;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cfg_c;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154__Vclpkg();
    ~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi87> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_agent__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_agent {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cfg_c> __PVT__cfg;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c> __PVT__cntxt;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_drv_c__Tz154> __PVT__drv;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_mon_c__Tz154> __PVT__mon;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154> __PVT__sqr;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz154> __PVT__drv_ap;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz154> __PVT__mon_ap;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    void __VnoInFunc_connect_analysis_ports(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_connect_cov_model(uvmt_fifo_tb__Syms* __restrict vlSymsp) {}
    virtual void __VnoInFunc_connect_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    void __VnoInFunc_connect_sequencer_and_driver(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_connect_trn_loggers(uvmt_fifo_tb__Syms* __restrict vlSymsp) {}
    void __VnoInFunc_create_components(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_get_and_set_cfg(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_get_and_set_cntxt(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    void __VnoInFunc_retrieve_vifs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154>& obj);

#endif  // guard
