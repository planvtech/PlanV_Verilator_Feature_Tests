// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CONFIG_DB___VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_CONFIG_DB___VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_waiter;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz70;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz7;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz30;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_config_db___Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component>, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz70>> __PVT__m_rsc;
    VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz7>> __PVT__m_waiters;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_config_db___Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_config_db___Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_config_db___Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_exists(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> cntxt, std::string inst_name, std::string field_name, CData/*0:0*/ spell_chk, CData/*0:0*/ &exists__Vfuncrtn);
    void __VnoInFunc_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> cntxt, std::string inst_name, std::string field_name, IData/*31:0*/ &value, CData/*0:0*/ &get__Vfuncrtn);
    void __VnoInFunc_set(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> cntxt, std::string inst_name, std::string field_name, IData/*31:0*/ value);
    VlCoroutine __VnoInFunc_wait_modified(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> cntxt, std::string inst_name, std::string field_name);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz30__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_config_db_ : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz30 {
  public:
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_config_db_(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_config_db_();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_config_db_>& obj);

#endif  // guard
