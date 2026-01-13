// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_POLICY__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_POLICY__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper>, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object>> __PVT__m_extensions;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object>> __PVT__m_policy_stack;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_clear_extension(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> ext_type);
    virtual void __VnoInFunc_clear_extensions(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_extension_exists(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> ext_type, CData/*0:0*/ &extension_exists__Vfuncrtn);
    virtual void __VnoInFunc_flush(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_get_active_object(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &get_active_object__Vfuncrtn);
    virtual void __VnoInFunc_get_active_object_depth(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_active_object_depth__Vfuncrtn);
    virtual void __VnoInFunc_get_extension(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> ext_type, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &get_extension__Vfuncrtn);
    virtual void __VnoInFunc_pop_active_object(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &pop_active_object__Vfuncrtn);
    virtual void __VnoInFunc_push_active_object(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> obj);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_set_extension(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &set_extension__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy>& obj);

#endif  // guard
