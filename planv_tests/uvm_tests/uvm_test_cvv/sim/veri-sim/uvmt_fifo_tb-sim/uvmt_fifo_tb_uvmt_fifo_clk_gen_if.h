// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVMT_FIFO_CLK_GEN_IF_H_
#define VERILATED_UVMT_FIFO_TB_UVMT_FIFO_CLK_GEN_IF_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvmt_fifo_clk_gen_if final {
  public:

    // DESIGN SPECIFIC STATE
    VL_OUT8(clk,0,0);
    VL_OUT8(reset_n,0,0);
    CData/*0:0*/ start_clk;
    CData/*0:0*/ __Vtrigprevexpr_h6568ff79__0;
    CData/*0:0*/ __Vtrigprevexpr_h8ae68869__0;
    CData/*0:0*/ __Vtrigprevexpr_h5029f6a9__0;
    CData/*0:0*/ __Vtrigprevexpr_hd633b7f2__0;
    double clk_period;
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk1__DOT____VforkParent;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvmt_fifo_clk_gen_if();
    ~uvmt_fifo_tb_uvmt_fifo_clk_gen_if();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvmt_fifo_clk_gen_if);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

std::string VL_TO_STRING(const uvmt_fifo_tb_uvmt_fifo_clk_gen_if* obj);

#endif  // guard
