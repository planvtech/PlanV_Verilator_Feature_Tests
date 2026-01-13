// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_RESOURCE_POOL__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_RESOURCE_POOL__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg.h"
#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_types__Vclpkg.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03aget_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tree_printer;


class uvmt_fifo_tb__Syms;
struct uvmt_fifo_tb_rsrc_info_t__struct__0 {
    std::string __PVT__scope;
    IData/*31:0*/ __PVT__precedence;

    bool operator==(const uvmt_fifo_tb_rsrc_info_t__struct__0& rhs) const {
        return __PVT__scope == rhs.__PVT__scope
            && __PVT__precedence == rhs.__PVT__precedence;
    }
    bool operator!=(const uvmt_fifo_tb_rsrc_info_t__struct__0& rhs) const {
        return !(*this == rhs);
    }

    bool operator<(const uvmt_fifo_tb_rsrc_info_t__struct__0& rhs) const {
        return std::tie(__PVT__scope, __PVT__precedence)
            <  std::tie(rhs.__PVT__scope, rhs.__PVT__precedence);
    }
};
template <>
struct VlIsCustomStruct<uvmt_fifo_tb_rsrc_info_t__struct__0> : public std::true_type {};

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base>, uvmt_fifo_tb_rsrc_info_t__struct__0> __PVT__ri_tab;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tree_printer> __PVT__print_resources__Vstatic__printer;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tree_printer> __PVT__dump__Vstatic__m_printer;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool> &get__Vfuncrtn);
    void __VnoInFunc_get_default_precedence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_default_precedence__Vfuncrtn);
    void __VnoInFunc_get_highest_precedence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> &q, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> &get_highest_precedence__Vfuncrtn);
    void __VnoInFunc_set_default_precedence(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ precedence);
    void __VnoInFunc_sort_by_precedence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> &q);
};

std::string VL_TO_STRING(const uvmt_fifo_tb_rsrc_info_t__struct__0& obj);

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8>> __PVT__rtab;
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base>, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8>> __PVT__ttab;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03aget_t>> __PVT__get_record;
    virtual void __VnoInFunc_delete(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc);
    void __VnoInFunc_dump(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ audit, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    void __VnoInFunc_dump_get_records(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_get_by_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> type_handle, CData/*0:0*/ rpterr, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> &get_by_name__Vfuncrtn);
    void __VnoInFunc_get_by_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> type_handle, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> &get_by_type__Vfuncrtn);
    virtual void __VnoInFunc_get_precedence(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> r, IData/*31:0*/ &get_precedence__Vfuncrtn);
    virtual void __VnoInFunc_get_scope(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc, std::string &scope, CData/*0:0*/ &get_scope__Vfuncrtn);
    void __VnoInFunc_lookup_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> type_handle, CData/*0:0*/ rpterr, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> &lookup_name__Vfuncrtn);
    void __VnoInFunc_lookup_regex(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string re, std::string scope, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> &lookup_regex__Vfuncrtn);
    void __VnoInFunc_lookup_regex_names(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> type_handle, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> &lookup_regex_names__Vfuncrtn);
    void __VnoInFunc_lookup_scope(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> &lookup_scope__Vfuncrtn);
    void __VnoInFunc_lookup_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string scope, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> type_handle, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> &lookup_type__Vfuncrtn);
    void __VnoInFunc_m_print_resources(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> rq, CData/*0:0*/ audit);
    void __VnoInFunc_print_resources(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> rq, CData/*0:0*/ audit);
    void __VnoInFunc_push_get_record(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, std::string scope, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc);
    void __VnoInFunc_set_name_override(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc, std::string scope);
    void __VnoInFunc_set_override(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc, std::string scope);
    virtual void __VnoInFunc_set_precedence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> r, IData/*31:0*/ p);
    void __VnoInFunc_set_priority(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc, IData/*31:0*/ pri);
    void __VnoInFunc_set_priority_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc, IData/*31:0*/ pri);
    void __VnoInFunc_set_priority_queue(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8> &q, IData/*31:0*/ &pri);
    void __VnoInFunc_set_priority_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc, IData/*31:0*/ pri);
    void __VnoInFunc_set_scope(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc, std::string scope);
    void __VnoInFunc_set_type_override(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc, std::string scope);
    void __VnoInFunc_spell_check(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string s, CData/*0:0*/ &spell_check__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool>& obj);

#endif  // guard
