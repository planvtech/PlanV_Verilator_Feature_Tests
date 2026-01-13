// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03AUVM_ANALYSIS_IMP_WR_INPUT__PI74__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03AUVM_ANALYSIS_IMP_WR_INPUT__PI74__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz181;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c;
class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74__Vclpkg();
    ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz181__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74 : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz181 {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c> __PVT__m_imp;
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    void __VnoInFunc_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_seq_item_c> t);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_prdr_c> imp);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvm_analysis_imp_wr_input__pi74>& obj);

#endif  // guard
