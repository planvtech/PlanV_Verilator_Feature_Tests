// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_MEM__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_MEM__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
#include "uvmt_fifo_tb_uvm_pkg.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_callback_iter__pi188;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam_cfg;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_string_pool__Tz337;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz336;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_cbs;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map_info;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_register_cb_uvm_reg_cbs;
    IData/*31:0*/ __PVT__m_max_size;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_max_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_max_size__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_object {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_locked;
    CData/*0:0*/ __PVT__m_read_in_progress;
    CData/*0:0*/ __PVT__m_write_in_progress;
    CData/*0:0*/ __PVT__m_is_powered_down;
    IData/*31:0*/ __PVT__m_n_bits;
    IData/*31:0*/ __PVT__m_has_cover;
    IData/*31:0*/ __PVT__m_cover_on;
    IData/*31:0*/ __PVT__m_lineno;
    QData/*63:0*/ __PVT__m_size;
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map>, CData/*0:0*/> __PVT__m_maps;
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg>, CData/*0:0*/> __PVT__m_vregs;
    std::string __PVT__m_access;
    std::string __PVT__m_fname;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> __PVT__m_parent;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> __PVT__m_backdoor;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_string_pool__Tz337> __PVT__m_hdl_paths_pool;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem_mam> __PVT__mam;
    void __VnoInFunc_Xadd_vregX(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg> vreg);
    void __VnoInFunc_Xcheck_accessX(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map_info> &map_info, CData/*0:0*/ &Xcheck_accessX__Vfuncrtn);
    void __VnoInFunc_Xdelete_vregX(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg> vreg);
    void __VnoInFunc_Xlock_modelX(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_XsampleX(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ addr, CData/*0:0*/ is_read, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map);
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_add_coverage(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ models);
    void __VnoInFunc_add_hdl_path(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<uvmt_fifo_tb_uvm_hdl_path_slice__struct__0> slices, std::string kind);
    void __VnoInFunc_add_hdl_path_slice(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, IData/*31:0*/ offset, IData/*31:0*/ size, CData/*0:0*/ first, std::string kind);
    void __VnoInFunc_add_map(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map);
    virtual void __VnoInFunc_backdoor_read(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    virtual void __VnoInFunc_backdoor_read_func(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw, IData/*31:0*/ &backdoor_read_func__Vfuncrtn);
    virtual void __VnoInFunc_backdoor_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    void __VnoInFunc_build_coverage(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ models, IData/*31:0*/ &build_coverage__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_burst_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, VlQueue<QData/*63:0*/> &value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    virtual VlCoroutine __VnoInFunc_burst_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, VlQueue<QData/*63:0*/> value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    void __VnoInFunc_clear_hdl_path(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string kind);
    virtual void __VnoInFunc_clone(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &clone__Vfuncrtn);
    void __VnoInFunc_configure(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> parent, std::string hdl_path);
    virtual void __VnoInFunc_convert2string(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &convert2string__Vfuncrtn);
    virtual void __VnoInFunc_do_compare(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer> comparer, CData/*0:0*/ &do_compare__Vfuncrtn);
    virtual void __VnoInFunc_do_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs);
    virtual void __VnoInFunc_do_pack(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    virtual void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual VlCoroutine __VnoInFunc_do_read(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    virtual void __VnoInFunc_do_unpack(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    virtual VlCoroutine __VnoInFunc_do_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    virtual void __VnoInFunc_get_access(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, std::string &get_access__Vfuncrtn);
    virtual void __VnoInFunc_get_address(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ offset, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, QData/*63:0*/ &get_address__Vfuncrtn);
    virtual void __VnoInFunc_get_addresses(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ offset, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlQueue<QData/*63:0*/> &addr, IData/*31:0*/ &get_addresses__Vfuncrtn);
    void __VnoInFunc_get_backdoor(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ inherited, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> &get_backdoor__Vfuncrtn);
    virtual void __VnoInFunc_get_block(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> &get_block__Vfuncrtn);
    virtual void __VnoInFunc_get_coverage(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ is_on, CData/*0:0*/ &get_coverage__Vfuncrtn);
    void __VnoInFunc_get_default_map(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> &get_default_map__Vfuncrtn);
    void __VnoInFunc_get_frontdoor(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor> &get_frontdoor__Vfuncrtn);
    void __VnoInFunc_get_full_hdl_path(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat>> &paths, std::string kind, std::string separator);
    virtual void __VnoInFunc_get_full_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_full_name__Vfuncrtn);
    void __VnoInFunc_get_hdl_path(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_hdl_path_concat>> &paths, std::string kind);
    void __VnoInFunc_get_hdl_path_kinds(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<std::string> &kinds);
    void __VnoInFunc_get_local_map(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> &get_local_map__Vfuncrtn);
    virtual void __VnoInFunc_get_maps(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map>> &maps);
    void __VnoInFunc_get_n_bits(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_n_bits__Vfuncrtn);
    void __VnoInFunc_get_n_bytes(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_n_bytes__Vfuncrtn);
    virtual void __VnoInFunc_get_n_maps(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_n_maps__Vfuncrtn);
    virtual void __VnoInFunc_get_offset(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ offset, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, QData/*63:0*/ &get_offset__Vfuncrtn);
    virtual void __VnoInFunc_get_parent(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> &get_parent__Vfuncrtn);
    virtual void __VnoInFunc_get_rights(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, std::string &get_rights__Vfuncrtn);
    void __VnoInFunc_get_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ &get_size__Vfuncrtn);
    virtual void __VnoInFunc_get_vfield_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field> &get_vfield_by_name__Vfuncrtn);
    virtual void __VnoInFunc_get_virtual_fields(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg_field>> &fields);
    virtual void __VnoInFunc_get_virtual_registers(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg>> &regs);
    virtual void __VnoInFunc_get_vreg_by_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg> &get_vreg_by_name__Vfuncrtn);
    virtual void __VnoInFunc_get_vreg_by_offset(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ offset, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_vreg> &get_vreg_by_offset__Vfuncrtn);
    virtual void __VnoInFunc_has_coverage(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ models, CData/*0:0*/ &has_coverage__Vfuncrtn);
    void __VnoInFunc_has_hdl_path(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string kind, CData/*0:0*/ &has_hdl_path__Vfuncrtn);
    void __VnoInFunc_is_in_map(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, CData/*0:0*/ &is_in_map__Vfuncrtn);
    virtual void __VnoInFunc_peek(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ &value, std::string kind, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    virtual void __VnoInFunc_poke(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ value, std::string kind, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    virtual void __VnoInFunc_post_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    virtual void __VnoInFunc_post_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    virtual void __VnoInFunc_pre_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    virtual void __VnoInFunc_pre_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_read(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ &value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
    virtual void __VnoInFunc_sample(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ offset, CData/*0:0*/ is_read, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map);
    void __VnoInFunc_set_backdoor(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_backdoor> bkdr, std::string fname, IData/*31:0*/ lineno);
    virtual void __VnoInFunc_set_coverage(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ is_on, IData/*31:0*/ &set_coverage__Vfuncrtn);
    void __VnoInFunc_set_frontdoor(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_frontdoor> ftdr, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, std::string fname, IData/*31:0*/ lineno);
    virtual void __VnoInFunc_set_offset(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, QData/*63:0*/ offset, CData/*0:0*/ unmapped);
    virtual void __VnoInFunc_set_parent(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_block> parent);
    virtual VlCoroutine __VnoInFunc_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, QData/*63:0*/ size, IData/*31:0*/ n_bits, std::string access, IData/*31:0*/ has_coverage);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem>& obj);

#endif  // guard
