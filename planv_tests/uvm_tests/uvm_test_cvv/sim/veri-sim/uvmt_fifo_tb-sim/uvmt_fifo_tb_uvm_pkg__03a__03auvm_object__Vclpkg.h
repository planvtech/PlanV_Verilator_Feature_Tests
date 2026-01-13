// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_OBJECT__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_OBJECT__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_copier;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_void;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__m_inst_count;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_object__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_inst_count(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_inst_count__Vfuncrtn);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_type__Vfuncrtn);
    void __VnoInFunc_get_uvm_seeding(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &get_uvm_seeding__Vfuncrtn);
    void __VnoInFunc_set_uvm_seeding(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ enable);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_void__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_void {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__m_inst_id;
    std::string __PVT__m_leaf_name;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc____05Fm_uvm_field_automation(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> tmp_data___05F, IData/*27:0*/ what___05F, std::string str___05F);
    virtual void __VnoInFunc_clone(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &clone__Vfuncrtn);
    void __VnoInFunc_compare(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer> comparer, CData/*0:0*/ &compare__Vfuncrtn);
    virtual void __VnoInFunc_convert2string(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &convert2string__Vfuncrtn);
    void __VnoInFunc_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_copier> copier);
    virtual void __VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn);
    virtual void __VnoInFunc_do_compare(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer> comparer, CData/*0:0*/ &do_compare__Vfuncrtn);
    virtual void __VnoInFunc_do_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs);
    virtual void __VnoInFunc_do_execute_op(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op> op);
    virtual void __VnoInFunc_do_pack(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    virtual void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual void __VnoInFunc_do_record(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> recorder);
    virtual void __VnoInFunc_do_unpack(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    virtual void __VnoInFunc_get_full_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_full_name__Vfuncrtn);
    virtual void __VnoInFunc_get_inst_id(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_inst_id__Vfuncrtn);
    virtual void __VnoInFunc_get_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_name__Vfuncrtn);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_m_get_report_object(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_object> &m_get_report_object__Vfuncrtn);
    void __VnoInFunc_m_pack(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> &packer);
    void __VnoInFunc_m_unpack_post(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer, IData/*31:0*/ &m_unpack_post__Vfuncrtn);
    void __VnoInFunc_m_unpack_pre(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> &packer);
    virtual void __VnoInFunc_m_unsupported_set_local(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc);
    void __VnoInFunc_pack(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*0:0*/> &bitstream, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer, IData/*31:0*/ &pack__Vfuncrtn);
    void __VnoInFunc_pack_bytes(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &bytestream, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer, IData/*31:0*/ &pack_bytes__Vfuncrtn);
    void __VnoInFunc_pack_ints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<IData/*31:0*/> &intstream, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer, IData/*31:0*/ &pack_ints__Vfuncrtn);
    void __VnoInFunc_pack_longints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<QData/*63:0*/> &longintstream, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer, IData/*31:0*/ &pack_longints__Vfuncrtn);
    void __VnoInFunc_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    void __VnoInFunc_record(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> recorder);
    void __VnoInFunc_reseed(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_set_local(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> rsrc);
    virtual void __VnoInFunc_set_name(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    void __VnoInFunc_sprint(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer, std::string &sprint__Vfuncrtn);
    void __VnoInFunc_unpack(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*0:0*/> &bitstream, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer, IData/*31:0*/ &unpack__Vfuncrtn);
    void __VnoInFunc_unpack_bytes(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &bytestream, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer, IData/*31:0*/ &unpack_bytes__Vfuncrtn);
    void __VnoInFunc_unpack_ints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<IData/*31:0*/> &intstream, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer, IData/*31:0*/ &unpack_ints__Vfuncrtn);
    void __VnoInFunc_unpack_longints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<QData/*63:0*/> &longintstream, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer, IData/*31:0*/ &unpack_longints__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_object(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_object();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object>& obj);

#endif  // guard
