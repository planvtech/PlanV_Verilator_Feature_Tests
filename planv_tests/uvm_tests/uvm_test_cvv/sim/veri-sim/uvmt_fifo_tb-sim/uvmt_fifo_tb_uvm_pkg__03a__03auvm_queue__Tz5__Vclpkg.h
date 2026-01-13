// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_QUEUE__TZ5__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_QUEUE__TZ5__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz348;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5> __PVT__m_global_queue;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_global(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ index, std::string &get_global__Vfuncrtn);
    void __VnoInFunc_get_global_queue(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5> &get_global_queue__Vfuncrtn);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz348> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __Vtrigprevexpr_hd90cdde5__0;
    VlQueue<std::string> __PVT__queue;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_convert2string(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &convert2string__Vfuncrtn);
    void __VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn);
    virtual void __VnoInFunc_delete(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ index);
    virtual void __VnoInFunc_do_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs);
    virtual void __VnoInFunc_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ index, std::string &get__Vfuncrtn);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_insert(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ index, std::string item);
    virtual void __VnoInFunc_pop_back(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &pop_back__Vfuncrtn);
    virtual void __VnoInFunc_pop_front(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &pop_front__Vfuncrtn);
    virtual void __VnoInFunc_push_back(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string item);
    virtual void __VnoInFunc_push_front(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string item);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &size__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_wait_until_not_empty(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz5>& obj);

#endif  // guard
