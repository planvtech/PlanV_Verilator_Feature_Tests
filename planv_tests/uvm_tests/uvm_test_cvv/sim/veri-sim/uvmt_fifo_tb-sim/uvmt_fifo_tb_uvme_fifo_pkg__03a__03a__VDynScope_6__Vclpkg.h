// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03A__VDYNSCOPE_6__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVME_FIFO_PKG__03A__03A__VDYNSCOPE_6__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_random_seq_c;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154;
class uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz155;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6__Vclpkg();
    ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6 : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_random_seq_c> __PVT__wr_seq;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz154> __PVT__wr_sqr;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_rd_random_seq_c> __PVT__rd_seq;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_base_sqr_c__Tz155> __PVT__rd_sqr;
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03a__VDynScope_6>& obj);

#endif  // guard
