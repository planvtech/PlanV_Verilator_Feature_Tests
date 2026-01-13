// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_RESOURCE_DB__TZ3__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_RESOURCE_DB__TZ3__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz3__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz3__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz3__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz3__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_dump(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_get_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, CData/*0:0*/ rpterr, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3> &get_by_name__Vfuncrtn);
    void __VnoInFunc_get_by_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3> &get_by_type__Vfuncrtn);
    void __VnoInFunc_m_show_msg(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string id, std::string rtype, std::string action, std::string scope, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3> rsrc);
    void __VnoInFunc_read_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, uvmt_fifo_tb_uvma_rd_if* &val, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor, CData/*0:0*/ &read_by_name__Vfuncrtn);
    void __VnoInFunc_read_by_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, uvmt_fifo_tb_uvma_rd_if* &val, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor, CData/*0:0*/ &read_by_type__Vfuncrtn);
    void __VnoInFunc_set(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, uvmt_fifo_tb_uvma_rd_if* val, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor);
    void __VnoInFunc_set_anonymous(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, uvmt_fifo_tb_uvma_rd_if* val, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor);
    void __VnoInFunc_set_default(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3> &set_default__Vfuncrtn);
    void __VnoInFunc_set_override(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, uvmt_fifo_tb_uvma_rd_if* val, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor);
    void __VnoInFunc_set_override_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, uvmt_fifo_tb_uvma_rd_if* val, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor);
    void __VnoInFunc_set_override_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, uvmt_fifo_tb_uvma_rd_if* val, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor);
    void __VnoInFunc_write_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, uvmt_fifo_tb_uvma_rd_if* val, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor, CData/*0:0*/ &write_by_name__Vfuncrtn);
    void __VnoInFunc_write_by_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, uvmt_fifo_tb_uvma_rd_if* val, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> accessor, CData/*0:0*/ &write_by_type__Vfuncrtn);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz3 : public virtual VlClass {
  public:
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz3(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz3();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_db__Tz3>& obj);

#endif  // guard
