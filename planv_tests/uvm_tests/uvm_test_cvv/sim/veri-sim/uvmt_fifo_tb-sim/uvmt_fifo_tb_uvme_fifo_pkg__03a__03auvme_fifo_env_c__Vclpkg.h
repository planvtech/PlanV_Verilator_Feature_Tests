// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03AUVME_FIFO_ENV_C__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03AUVME_FIFO_ENV_C__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz154;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_analysis_port__Tz155;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi72;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_env;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz155;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_act__pi78;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_exp__pi80;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_rd_input__pi75;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_act__pi77;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_exp__pi79;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_random_vseq_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_vsqr_c;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c__Vclpkg();
    ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi72> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_env__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_env {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c> __PVT__cfg;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c> __PVT__cntxt;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c> __PVT__predictor;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_sb_c> __PVT__scoreboard;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_vsqr_c> __PVT__vsequencer;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz154> __PVT__write_agent;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_agent_c__Tz155> __PVT__read_agent;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_assemble_vsequencer(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_assign_cfg(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_assign_cntxt(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_connect_cov_model(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_connect_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_connect_predictor(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_connect_scoreboard(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_create_agents(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_create_cov_model(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_create_env_components(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_create_vsequencer(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_end_of_elaboration_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_retrieve_vifs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_run_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c>& obj);

#endif  // guard
