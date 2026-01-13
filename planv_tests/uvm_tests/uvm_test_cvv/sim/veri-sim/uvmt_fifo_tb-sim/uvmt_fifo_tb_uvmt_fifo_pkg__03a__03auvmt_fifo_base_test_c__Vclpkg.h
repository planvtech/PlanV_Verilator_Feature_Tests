// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVMT_FIFO_PKG__03A__03AUVMT_FIFO_BASE_TEST_C__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVMT_FIFO_PKG__03A__03AUVMT_FIFO_BASE_TEST_C__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi68;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_test;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cfg_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_vsqr_c;
class uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c;
class uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_cfg_c;
class uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg();
    ~uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__pi68> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_test__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_test {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __Vtrigprevexpr_h34f2bc4d__0;
    IData/*31:0*/ __PVT__success;
    VlStdRandomizer __PVT__stdrand;
    VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_cfg_c> __PVT__test_cfg;
    VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_test_randvars_c> __PVT__test_randvars;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c> __PVT__env_cfg;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c> __PVT__env_cntxt;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_env_c> __PVT__env;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_vsqr_c> __PVT__vsqr;
    uvmt_fifo_tb_uvmt_fifo_clk_gen_if* __PVT__rd_clk_gen_vif;
    uvmt_fifo_tb_uvmt_fifo_clk_gen_if* __PVT__wr_clk_gen_vif;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    void __VnoInFunc___VStdrand_h80dc4f1c__0(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VStdrand_h80dc4f1c__0__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_assign_cfg(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_assign_cntxt(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_build_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_connect_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_create_cfg_and_cntxt(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_create_components(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_create_env(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_env_cfg__DT__agent_cfg_cons_setup_constraint(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_env_cfg_con_setup_constraint(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_randomize_test(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_report_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    void __VnoInFunc_retrieve_vifs(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_run_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    void __VnoInFunc_test_cfg__DT__timeout_default_cons_setup_constraint(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_watchdog_timer(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    VlCoroutine __VnoInFunc_watchdog_timer____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk1__DOT____VforkParent);
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvmt_fifo_pkg__03a__03auvmt_fifo_base_test_c>& obj);

#endif  // guard
