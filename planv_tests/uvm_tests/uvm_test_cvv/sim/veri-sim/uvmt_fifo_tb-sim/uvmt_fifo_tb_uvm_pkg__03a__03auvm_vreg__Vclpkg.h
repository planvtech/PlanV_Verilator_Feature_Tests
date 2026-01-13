// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_VREG__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_VREG__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03asemaphore;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi190;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi191;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_policy;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_cbs;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field_cbs;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_register_cb_uvm_vreg_cbs;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__locked;
    CData/*0:0*/ __PVT__is_static;
    CData/*0:0*/ __PVT__read_in_progress;
    CData/*0:0*/ __PVT__write_in_progress;
    IData/*31:0*/ __PVT__n_bits;
    IData/*31:0*/ __PVT__n_used_bits;
    IData/*31:0*/ __PVT__incr;
    IData/*31:0*/ __PVT__lineno;
    QData/*63:0*/ __PVT__offset;
    QData/*63:0*/ __PVT__size;
    std::string __PVT__fname;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> __PVT__parent;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field>> __PVT__fields;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> __PVT__mem;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region> __PVT__region;
    VlClassRef<uvmt_fifo_tb_std__03a__03asemaphore> __PVT__atomic;
    VlCoroutine __VnoInFunc_XatomicX(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ on);
    void __VnoInFunc_Xlock_modelX(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_add_field(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field> field);
    virtual void __VnoInFunc_allocate(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ n, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam> mam, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_policy> alloc, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region> &allocate__Vfuncrtn);
    virtual void __VnoInFunc_clone(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &clone__Vfuncrtn);
    void __VnoInFunc_configure(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> mem, QData/*63:0*/ size, QData/*63:0*/ offset, IData/*31:0*/ incr);
    virtual void __VnoInFunc_convert2string(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &convert2string__Vfuncrtn);
    virtual void __VnoInFunc_do_compare(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer> comparer, CData/*0:0*/ &do_compare__Vfuncrtn);
    virtual void __VnoInFunc_do_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs);
    virtual void __VnoInFunc_do_pack(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    virtual void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual void __VnoInFunc_do_unpack(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    virtual void __VnoInFunc_get_access(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, std::string &get_access__Vfuncrtn);
    virtual void __VnoInFunc_get_address(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, QData/*63:0*/ &get_address__Vfuncrtn);
    virtual void __VnoInFunc_get_block(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> &get_block__Vfuncrtn);
    virtual void __VnoInFunc_get_field_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field> &get_field_by_name__Vfuncrtn);
    virtual void __VnoInFunc_get_fields(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field>> &fields);
    virtual void __VnoInFunc_get_full_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_full_name__Vfuncrtn);
    virtual void __VnoInFunc_get_incr(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_incr__Vfuncrtn);
    virtual void __VnoInFunc_get_maps(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map>> &maps);
    virtual void __VnoInFunc_get_memory(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> &get_memory__Vfuncrtn);
    virtual void __VnoInFunc_get_n_bytes(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_n_bytes__Vfuncrtn);
    virtual void __VnoInFunc_get_n_maps(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_n_maps__Vfuncrtn);
    virtual void __VnoInFunc_get_n_memlocs(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_n_memlocs__Vfuncrtn);
    virtual void __VnoInFunc_get_offset_in_memory(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, QData/*63:0*/ &get_offset_in_memory__Vfuncrtn);
    virtual void __VnoInFunc_get_parent(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> &get_parent__Vfuncrtn);
    virtual void __VnoInFunc_get_region(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_region> &get_region__Vfuncrtn);
    virtual void __VnoInFunc_get_rights(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, std::string &get_rights__Vfuncrtn);
    virtual void __VnoInFunc_get_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_size__Vfuncrtn);
    virtual void __VnoInFunc_implement(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ n, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> mem, QData/*63:0*/ offset, IData/*31:0*/ incr, CData/*0:0*/ &implement__Vfuncrtn);
    void __VnoInFunc_is_in_map(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, CData/*0:0*/ &is_in_map__Vfuncrtn);
    virtual void __VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, IData/*31:0*/ &status, QData/*63:0*/ &value, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    virtual void __VnoInFunc_poke(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, IData/*31:0*/ &status, QData/*63:0*/ value, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    virtual void __VnoInFunc_post_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, QData/*63:0*/ &rdat, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, IData/*31:0*/ &status);
    virtual void __VnoInFunc_post_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, QData/*63:0*/ wdat, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, IData/*31:0*/ &status);
    virtual void __VnoInFunc_pre_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, IData/*31:0*/ &path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> &map);
    virtual void __VnoInFunc_pre_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, QData/*63:0*/ &wdat, IData/*31:0*/ &path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> &map);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, IData/*31:0*/ &status, QData/*63:0*/ &value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    virtual void __VnoInFunc_release_region(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string kind);
    virtual void __VnoInFunc_set_parent(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> parent);
    virtual VlCoroutine __VnoInFunc_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ idx, IData/*31:0*/ &status, QData/*63:0*/ value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, IData/*31:0*/ n_bits);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg>& obj);

#endif  // guard
