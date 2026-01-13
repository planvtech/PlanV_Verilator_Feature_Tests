// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVMA_RD_IF_H_
#define VERILATED_UVMT_FIFO_TB_UVMA_RD_IF_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvma_rd_if final {
  public:

    // DESIGN SPECIFIC STATE
    VL_IN8(clk,0,0);
    VL_IN8(reset_n,0,0);
    CData/*7:0*/ data;
    CData/*0:0*/ en;
    CData/*0:0*/ empty;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvma_rd_if();
    ~uvmt_fifo_tb_uvma_rd_if();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvma_rd_if);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

std::string VL_TO_STRING(const uvmt_fifo_tb_uvma_rd_if* obj);

#endif  // guard
