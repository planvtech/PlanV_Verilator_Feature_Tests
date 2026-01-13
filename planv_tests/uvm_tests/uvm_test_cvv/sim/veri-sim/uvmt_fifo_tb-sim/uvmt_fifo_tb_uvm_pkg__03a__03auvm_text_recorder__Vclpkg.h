// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TEXT_RECORDER__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_TEXT_RECORDER__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi256;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_recorder;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_tr_database;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_tr_stream;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_database;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_recorder__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_recorder__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_recorder__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_recorder__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi256> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_recorder : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__filename_set;
    VlWide<3600>/*115199:0*/ __Vfunc_uvm_string_to_bits__31__Vfuncout;
    VlQueue<std::string> __PVT__m_object_names;
    std::string __PVT__filename;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_tr_database> __PVT__m_text_db;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_begin_tr(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string txtype, IData/*31:0*/ stream, std::string nm, std::string label, std::string desc, QData/*63:0*/ begin_time, IData/*31:0*/ &begin_tr__Vfuncrtn);
    virtual void __VnoInFunc_check_handle_kind(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string htype, IData/*31:0*/ handle, IData/*31:0*/ &check_handle_kind__Vfuncrtn);
    void __VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn);
    virtual void __VnoInFunc_create_stream(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, std::string t, std::string scope, IData/*31:0*/ &create_stream__Vfuncrtn);
    virtual void __VnoInFunc_do_close(uvmt_fifo_tb__Syms* __restrict vlSymsp, QData/*63:0*/ close_time);
    virtual void __VnoInFunc_do_free(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_do_open(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_tr_stream> stream, QData/*63:0*/ open_time, std::string type_name);
    virtual void __VnoInFunc_do_record_field(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlWide<128>/*4095:0*/ value, IData/*31:0*/ size, IData/*27:0*/ radix);
    virtual void __VnoInFunc_do_record_field_int(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, QData/*63:0*/ value, IData/*31:0*/ size, IData/*27:0*/ radix);
    virtual void __VnoInFunc_do_record_field_real(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, double value);
    virtual void __VnoInFunc_do_record_generic(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, std::string value, std::string type_name);
    virtual void __VnoInFunc_do_record_object(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> value);
    virtual void __VnoInFunc_do_record_string(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, std::string value);
    virtual void __VnoInFunc_do_record_time(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, QData/*63:0*/ value);
    virtual void __VnoInFunc_end_tr(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ handle, QData/*63:0*/ end_time);
    virtual void __VnoInFunc_free_tr(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ handle);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    virtual void __VnoInFunc_link_tr(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ h1, IData/*31:0*/ h2, std::string relation);
    void __VnoInFunc_m_current_context(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, std::string &m_current_context__Vfuncrtn);
    virtual void __VnoInFunc_m_set_attribute(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ txh, std::string nm, std::string value);
    virtual void __VnoInFunc_open_file(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &open_file__Vfuncrtn);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_set_attribute(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ txh, std::string nm, VlWide<32>/*1023:0*/ value, IData/*27:0*/ radix, IData/*31:0*/ numbits);
    void __VnoInFunc_write_attribute(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string nm, VlWide<128>/*4095:0*/ value, IData/*27:0*/ radix, IData/*31:0*/ numbits);
    void __VnoInFunc_write_attribute_int(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string nm, QData/*63:0*/ value, IData/*27:0*/ radix, IData/*31:0*/ numbits);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_recorder(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_recorder();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_text_recorder>& obj);

#endif  // guard
