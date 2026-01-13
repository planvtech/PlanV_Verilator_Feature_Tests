// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_POOL__TZ5_TBZ337__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_POOL__TZ5_TBZ337__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz405;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz336;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337> __PVT__m_global_pool;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_global(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz336> &get_global__Vfuncrtn);
    void __VnoInFunc_get_global_pool(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337> &get_global_pool__Vfuncrtn);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz405> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz336>> __PVT__pool;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_add(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz336> item);
    void __VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn);
    virtual void __VnoInFunc_delete(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key);
    virtual void __VnoInFunc_do_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs);
    virtual void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual void __VnoInFunc_exists(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key, IData/*31:0*/ &exists__Vfuncrtn);
    virtual void __VnoInFunc_first(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &key, IData/*31:0*/ &first__Vfuncrtn);
    virtual void __VnoInFunc_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz336> &get__Vfuncrtn);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_last(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &key, IData/*31:0*/ &last__Vfuncrtn);
    virtual void __VnoInFunc_next(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &key, IData/*31:0*/ &next__Vfuncrtn);
    virtual void __VnoInFunc_num(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &num__Vfuncrtn);
    virtual void __VnoInFunc_prev(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &key, IData/*31:0*/ &prev__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz337>& obj);

#endif  // guard
