// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TLM_GENERIC_PAYLOAD__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TLM_GENERIC_PAYLOAD__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi194;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_extension_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_generic_payload;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_generic_payload__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_generic_payload__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_generic_payload__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_generic_payload__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi194> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_generic_payload : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_dmi;
    IData/*31:0*/ __PVT__m_command;
    IData/*31:0*/ __PVT__m_length;
    IData/*31:0*/ __PVT__m_response_status;
    IData/*31:0*/ __PVT__m_byte_enable_length;
    IData/*31:0*/ __PVT__m_streaming_width;
    QData/*63:0*/ __PVT__m_address;
    VlQueue<CData/*7:0*/> __PVT__m_data;
    VlQueue<CData/*7:0*/> __PVT__m_byte_enable;
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_extension_base>, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_extension_base>> __PVT__m_extensions;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_extension_base>> __PVT__m_rand_exts;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_clear_extension(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_extension_base> ext_handle);
    void __VnoInFunc_clear_extensions(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_convert2string(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &convert2string__Vfuncrtn);
    void __VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn);
    void __VnoInFunc_do_compare(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer> comparer, CData/*0:0*/ &do_compare__Vfuncrtn);
    void __VnoInFunc_do_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs);
    void __VnoInFunc_do_pack(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    void __VnoInFunc_do_record(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> recorder);
    void __VnoInFunc_do_unpack(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> packer);
    virtual void __VnoInFunc_get_address(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ &get_address__Vfuncrtn);
    virtual void __VnoInFunc_get_byte_enable(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &p);
    virtual void __VnoInFunc_get_byte_enable_length(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_byte_enable_length__Vfuncrtn);
    virtual void __VnoInFunc_get_command(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_command__Vfuncrtn);
    virtual void __VnoInFunc_get_data(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &p);
    virtual void __VnoInFunc_get_data_length(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_data_length__Vfuncrtn);
    void __VnoInFunc_get_extension(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_extension_base> ext_handle, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_extension_base> &get_extension__Vfuncrtn);
    void __VnoInFunc_get_num_extensions(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_num_extensions__Vfuncrtn);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_response_status(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_response_status__Vfuncrtn);
    virtual void __VnoInFunc_get_response_string(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_response_string__Vfuncrtn);
    virtual void __VnoInFunc_get_streaming_width(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_streaming_width__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_is_dmi_allowed(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_dmi_allowed__Vfuncrtn);
    virtual void __VnoInFunc_is_read(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_read__Vfuncrtn);
    virtual void __VnoInFunc_is_response_error(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_response_error__Vfuncrtn);
    virtual void __VnoInFunc_is_response_ok(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_response_ok__Vfuncrtn);
    virtual void __VnoInFunc_is_write(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_write__Vfuncrtn);
    void __VnoInFunc_post_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_pre_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_set_address(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ addr);
    virtual void __VnoInFunc_set_byte_enable(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &p);
    virtual void __VnoInFunc_set_byte_enable_length(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ length);
    virtual void __VnoInFunc_set_command(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ command);
    virtual void __VnoInFunc_set_data(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<CData/*7:0*/> &p);
    virtual void __VnoInFunc_set_data_length(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ length);
    virtual void __VnoInFunc_set_dmi_allowed(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ dmi);
    void __VnoInFunc_set_extension(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_extension_base> ext, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_extension_base> &set_extension__Vfuncrtn);
    virtual void __VnoInFunc_set_read(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_set_response_status(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ status);
    virtual void __VnoInFunc_set_streaming_width(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ width);
    virtual void __VnoInFunc_set_write(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_generic_payload(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_generic_payload();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tlm_generic_payload>& obj);

#endif  // guard
