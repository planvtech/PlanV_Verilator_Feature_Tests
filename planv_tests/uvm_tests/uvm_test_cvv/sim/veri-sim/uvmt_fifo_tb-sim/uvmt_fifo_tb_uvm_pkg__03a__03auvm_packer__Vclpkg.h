// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_PACKER__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_PACKER__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi10;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    VlQueue<CData/*0:0*/> __PVT__bitstream;
    VlQueue<CData/*0:0*/> __PVT__fabitstream;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_default(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> &get_default__Vfuncrtn);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi10> &get_type__Vfuncrtn);
    void __VnoInFunc_set_default(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__reverse_order;
    CData/*7:0*/ __PVT__byte_size;
    CData/*0:0*/ __PVT__nopack;
    IData/*31:0*/ __PVT__m_pack_iter;
    IData/*31:0*/ __PVT__m_unpack_iter;
    IData/*31:0*/ __PVT__word_size;
    VlWide<1024>/*32767:0*/ __PVT__m_bits;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory> __PVT__m_factory;
    VlAssocArray<IData/*31:0*/, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object>> __PVT__m_object_references;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn);
    void __VnoInFunc_enough_bits(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ needed, std::string id, CData/*0:0*/ &enough_bits__Vfuncrtn);
    virtual void __VnoInFunc_flush(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_packed_bits(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*0:0*/> &stream);
    virtual void __VnoInFunc_get_packed_bytes(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &stream);
    virtual void __VnoInFunc_get_packed_ints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<IData/*31:0*/> &stream);
    virtual void __VnoInFunc_get_packed_longints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<QData/*63:0*/> &stream);
    virtual void __VnoInFunc_get_packed_size(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_packed_size__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    void __VnoInFunc_index_error(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ index, std::string id, IData/*31:0*/ sz);
    virtual void __VnoInFunc_is_null(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_null__Vfuncrtn);
    virtual void __VnoInFunc_is_object_wrapper(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_object_wrapper__Vfuncrtn);
    virtual void __VnoInFunc_pack_bits(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*0:0*/> &value, IData/*31:0*/ size);
    virtual void __VnoInFunc_pack_bytes(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &value, IData/*31:0*/ size);
    virtual void __VnoInFunc_pack_field(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlWide<128>/*4095:0*/ value, IData/*31:0*/ size);
    virtual void __VnoInFunc_pack_field_int(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ value, IData/*31:0*/ size);
    virtual void __VnoInFunc_pack_ints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<IData/*31:0*/> &value, IData/*31:0*/ size);
    virtual void __VnoInFunc_pack_object(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> value);
    virtual void __VnoInFunc_pack_object_with_meta(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> value);
    virtual void __VnoInFunc_pack_object_wrapper(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> value);
    virtual void __VnoInFunc_pack_real(uvmt_fifo_tb__Syms* __restrict vlSymsp, double value);
    virtual void __VnoInFunc_pack_string(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string value);
    virtual void __VnoInFunc_pack_time(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ value);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_set_packed_bits(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*0:0*/> &stream);
    virtual void __VnoInFunc_set_packed_bytes(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &stream);
    virtual void __VnoInFunc_set_packed_ints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<IData/*31:0*/> &stream);
    virtual void __VnoInFunc_set_packed_longints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<QData/*63:0*/> &stream);
    virtual void __VnoInFunc_unpack_bits(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*0:0*/> &value, IData/*31:0*/ size);
    virtual void __VnoInFunc_unpack_bytes(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &value, IData/*31:0*/ size);
    virtual void __VnoInFunc_unpack_field(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ size, VlWide<128>/*4095:0*/ &unpack_field__Vfuncrtn);
    virtual void __VnoInFunc_unpack_field_int(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ size, QData/*63:0*/ &unpack_field_int__Vfuncrtn);
    virtual void __VnoInFunc_unpack_ints(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<IData/*31:0*/> &value, IData/*31:0*/ size);
    virtual void __VnoInFunc_unpack_object(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> value);
    virtual void __VnoInFunc_unpack_object_with_meta(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &value);
    virtual void __VnoInFunc_unpack_object_wrapper(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &unpack_object_wrapper__Vfuncrtn);
    virtual void __VnoInFunc_unpack_real(uvmt_fifo_tb__Syms* __restrict vlSymsp, double &unpack_real__Vfuncrtn);
    virtual void __VnoInFunc_unpack_string(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &unpack_string__Vfuncrtn);
    virtual void __VnoInFunc_unpack_time(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ &unpack_time__Vfuncrtn);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer>& obj);

#endif  // guard
