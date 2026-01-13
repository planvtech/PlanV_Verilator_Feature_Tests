// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_STD__03A__03APROCESS__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_STD__03A__03APROCESS__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_std__03a__03aprocess__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_std__03a__03aprocess__Vclpkg();
    ~uvmt_fifo_tb_std__03a__03aprocess__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_std__03a__03aprocess__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_killQueue(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<VlClassRef<uvmt_fifo_tb_std__03a__03aprocess>> &processQueue);
    void __VnoInFunc_self(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> &self__Vfuncrtn);
};


class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_std__03a__03aprocess : public virtual VlClass {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __Vtrigprevexpr_h4b30777f__0;
    VlProcessRef __PVT__m_process;

    // INTERNAL VARIABLES
    VlRNG __Vm_rng;
    VlCoroutine __VnoInFunc_await(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_get_randstate(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_randstate__Vfuncrtn);
    void __VnoInFunc_kill(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_resume(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_set_randstate(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string s);
    void __VnoInFunc_set_status(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ s);
    void __VnoInFunc_srandom(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ seed);
    void __VnoInFunc_status(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &status__Vfuncrtn);
    void __VnoInFunc_suspend(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_std__03a__03aprocess(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    std::string to_string() const;
    std::string to_string_middle() const;
    ~uvmt_fifo_tb_std__03a__03aprocess() {}
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_std__03a__03aprocess>& obj);


//*** Below code from `systemc in Verilog file
// From `systemc at /home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../verilator/master/include/verilated_std.sv:196:21

template<> template<>
inline bool VlClassRef<uvmt_fifo_tb_std__03a__03aprocess>::operator==(const VlClassRef<uvmt_fifo_tb_std__03a__03aprocess>& rhs) const {
    if (!m_objp && !rhs.m_objp) return true;
    if (!m_objp || !rhs.m_objp) return false;
    return m_objp->__PVT__m_process == rhs.m_objp->__PVT__m_process;
};
template<> template<>
inline bool VlClassRef<uvmt_fifo_tb_std__03a__03aprocess>::operator!=(const VlClassRef<uvmt_fifo_tb_std__03a__03aprocess>& rhs) const {
    if (!m_objp && !rhs.m_objp) return false;
    if (!m_objp || !rhs.m_objp) return true;
    return m_objp->__PVT__m_process != rhs.m_objp->__PVT__m_process;
};
template<> template<>
inline bool VlClassRef<uvmt_fifo_tb_std__03a__03aprocess>::operator<(const VlClassRef<uvmt_fifo_tb_std__03a__03aprocess>& rhs) const {
    if (!m_objp && !rhs.m_objp) return false;
    if (!m_objp || !rhs.m_objp) return false;
    return m_objp->__PVT__m_process < rhs.m_objp->__PVT__m_process;
};
//*** Above code from `systemc in Verilog file


#endif  // guard
