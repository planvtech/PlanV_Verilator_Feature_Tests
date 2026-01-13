// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

VL_ATTR_COLD void uvmt_fifo_tb___024root___eval_initial__TOP(uvmt_fifo_tb___024root* vlSelf, VlProcessRef vlProcess);
VlCoroutine uvmt_fifo_tb___024root___eval_initial__TOP__Vtiming__0(uvmt_fifo_tb___024root* vlSelf, VlProcessRef vlProcess);
VlCoroutine uvmt_fifo_tb_uvmt_fifo_clk_gen_if___eval_initial__TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__Vtiming__0(uvmt_fifo_tb_uvmt_fifo_clk_gen_if* vlSelf, VlProcessRef vlProcess);
VlCoroutine uvmt_fifo_tb_uvmt_fifo_clk_gen_if___eval_initial__TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__Vtiming__0(uvmt_fifo_tb_uvmt_fifo_clk_gen_if* vlSelf, VlProcessRef vlProcess);

void uvmt_fifo_tb___024root___eval_initial(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_initial\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    uvmt_fifo_tb___024root___eval_initial__TOP(vlSelf, vlProcess);
    vlSelfRef.__Vm_traceActivity[1U] = 1U;
    uvmt_fifo_tb___024root___eval_initial__TOP__Vtiming__0(vlSelf, std::make_shared<VlProcess>());
    uvmt_fifo_tb_uvmt_fifo_clk_gen_if___eval_initial__TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__Vtiming__0((&vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if), std::make_shared<VlProcess>());
    uvmt_fifo_tb_uvmt_fifo_clk_gen_if___eval_initial__TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__Vtiming__0((&vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if), std::make_shared<VlProcess>());
}

VlCoroutine uvmt_fifo_tb___024root___eval_initial__TOP__Vtiming__0(uvmt_fifo_tb___024root* vlSelf, VlProcessRef vlProcess) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_initial__TOP__Vtiming__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    std::string __Vtask_run_test__24__test_name;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__25__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__26__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> TOP__uvm_pkg__DOT__run_test__Vstatic__top;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> TOP__uvm_pkg__DOT__run_test__Vstatic__cs;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz1__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, VlNull{}, "*"s, "wr_clk_gen_vif"s, (&vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if));
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz1__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, VlNull{}, "*"s, "rd_clk_gen_vif"s, (&vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if));
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz2__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, VlNull{}, "*.env*"s, "wr_vif"s, (&vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if));
    vlSymsp->TOP__uvm_pkg__03a__03auvm_config_db__Tz3__Vclpkg.__VnoInFunc_set(vlProcess, vlSymsp, VlNull{}, "*.env*"s, "rd_vif"s, (&vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if));
    vlSymsp->_vm_contextp__->dumpfile("waveform.vcd"s);
    vlSymsp->_traceDumpOpen();
    __Vtask_run_test__24__test_name = ""s;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__25__Vfuncout);
    TOP__uvm_pkg__DOT__run_test__Vstatic__cs = __Vfunc_get__25__Vfuncout;
    VL_NULL_CHECK(TOP__uvm_pkg__DOT__run_test__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 49)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__26__Vfuncout);
    TOP__uvm_pkg__DOT__run_test__Vstatic__top = __Vtask_get_root__26__Vfuncout;
    co_await VL_NULL_CHECK(TOP__uvm_pkg__DOT__run_test__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 50)->__VnoInFunc_run_test(vlProcess, vlSymsp, __Vtask_run_test__24__test_name);
    vlProcess->state(VlProcess::FINISHED);
    co_return;}

#ifdef VL_DEBUG
VL_ATTR_COLD void uvmt_fifo_tb___024root___dump_triggers__ico(const VlUnpacked<QData/*63:0*/, 1> &triggers, const std::string &tag);
#endif  // VL_DEBUG

void uvmt_fifo_tb___024root___eval_triggers__ico(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_triggers__ico\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.__VicoTriggered[0U] = ((0xfffffffffffffffeULL 
                                      & vlSelfRef.__VicoTriggered
                                      [0U]) | (IData)((IData)(vlSelfRef.__VicoFirstIteration)));
    vlSelfRef.__VicoFirstIteration = 0U;
    vlSelfRef.__VicoTriggered[0U] = ((0xffffffffffffffdfULL 
                                      & vlSelfRef.__VicoTriggered
                                      [0U]) | ((QData)((IData)(vlSelfRef.__VvifTrigger_h65ecbd10__1_Vtrigm_full)) 
                                               << 5U));
    vlSelfRef.__VvifTrigger_h65ecbd10__1_Vtrigm_full = 0U;
    vlSelfRef.__VicoTriggered[0U] = ((0xffffffffffffffefULL 
                                      & vlSelfRef.__VicoTriggered
                                      [0U]) | ((QData)((IData)(vlSelfRef.__VvifTrigger_h0e8631bc__2_Vtrigm_data)) 
                                               << 4U));
    vlSelfRef.__VvifTrigger_h0e8631bc__2_Vtrigm_data = 0U;
    vlSelfRef.__VicoTriggered[0U] = ((0xfffffffffffffff7ULL 
                                      & vlSelfRef.__VicoTriggered
                                      [0U]) | ((QData)((IData)(vlSelfRef.__VvifTrigger_h0e8631bc__1_Vtrigm_empty)) 
                                               << 3U));
    vlSelfRef.__VvifTrigger_h0e8631bc__1_Vtrigm_empty = 0U;
    vlSelfRef.__VicoTriggered[0U] = ((0xfffffffffffffffbULL 
                                      & vlSelfRef.__VicoTriggered
                                      [0U]) | ((QData)((IData)(vlSelfRef.__VvifTrigger_h0e8631bc__0_Vtrigm_clk)) 
                                               << 2U));
    vlSelfRef.__VvifTrigger_h0e8631bc__0_Vtrigm_clk = 0U;
    vlSelfRef.__VicoTriggered[0U] = ((0xfffffffffffffffdULL 
                                      & vlSelfRef.__VicoTriggered
                                      [0U]) | ((QData)((IData)(vlSelfRef.__VvifTrigger_h65ecbd10__0_Vtrigm_clk)) 
                                               << 1U));
    vlSelfRef.__VvifTrigger_h65ecbd10__0_Vtrigm_clk = 0U;
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        uvmt_fifo_tb___024root___dump_triggers__ico(vlSelfRef.__VicoTriggered, "ico"s);
    }
#endif
}

bool uvmt_fifo_tb___024root___trigger_anySet__ico(const VlUnpacked<QData/*63:0*/, 1> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___trigger_anySet__ico\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        if (in[n]) {
            return (1U);
        }
        n = ((IData)(1U) + n);
    } while ((1U > n));
    return (0U);
}

void uvmt_fifo_tb___024root___ico_comb__TOP__0(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___ico_comb__TOP__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin_next 
        = (0x0000001fU & ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin) 
                          + (1U & ((~ (IData)(vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__r_empty)) 
                                   & (IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.en)))));
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_gray_next 
        = (0x0000001fU & ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin_next) 
                          ^ VL_SHIFTR_III(5,5,32, (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin_next), 1U)));
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_empty_tmp 
        = ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_gray_next) 
           == (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_o));
}

void uvmt_fifo_tb___024root___ico_comb__TOP__1(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___ico_comb__TOP__1\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin_next 
        = (0x0000001fU & ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin) 
                          + (1U & ((~ (IData)(vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__w_full)) 
                                   & (IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.en)))));
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_gray_next 
        = (0x0000001fU & ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin_next) 
                          ^ VL_SHIFTR_III(5,5,32, (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin_next), 1U)));
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__r_ptr_gray_next 
        = ((0x00000018U & ((~ ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_o) 
                               >> 3U)) << 3U)) | (7U 
                                                  & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_o)));
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_full_tmp 
        = ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_gray_next) 
           == (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__r_ptr_gray_next));
    if (((IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.en) 
         & (~ (IData)(vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__w_full)))) {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[(0x0000000fU 
                                                                                & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin))] 
            = vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.data;
    }
    ([&]() {
            vlSelfRef.__VvifTrigger_h0e8631bc__2_Vtrigm_data = 1U;
        }(), vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.data) 
        = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data
        [(0x0000000fU & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin))];
}

void uvmt_fifo_tb___024root___eval_ico(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_ico\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if ((0x000000000000001cULL & vlSelfRef.__VicoTriggered
         [0U])) {
        uvmt_fifo_tb___024root___ico_comb__TOP__0(vlSelf);
    }
    if ((0x0000000000000022ULL & vlSelfRef.__VicoTriggered
         [0U])) {
        uvmt_fifo_tb___024root___ico_comb__TOP__1(vlSelf);
        vlSelfRef.__Vm_traceActivity[2U] = 1U;
    }
}

bool uvmt_fifo_tb___024root___eval_phase__ico(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_phase__ico\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VicoExecute;
    // Body
    uvmt_fifo_tb___024root___eval_triggers__ico(vlSelf);
    __VicoExecute = uvmt_fifo_tb___024root___trigger_anySet__ico(vlSelfRef.__VicoTriggered);
    if (__VicoExecute) {
        uvmt_fifo_tb___024root___eval_ico(vlSelf);
    }
    return (__VicoExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void uvmt_fifo_tb___024root___dump_triggers__act(const VlUnpacked<QData/*63:0*/, 2> &triggers, const std::string &tag);
#endif  // VL_DEBUG

void uvmt_fifo_tb___024root___eval_triggers__act(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_triggers__act\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __Vtrigprevexpr_hd86c879f__0;
    __Vtrigprevexpr_hd86c879f__0 = 0;
    // Body
    vlSelfRef.__VactTriggered[1U] = ((0xffffffffffffffefULL 
                                      & vlSelfRef.__VactTriggered
                                      [1U]) | ((QData)((IData)(vlSelfRef.__VvifTrigger_h65ecbd10__1_Vtrigm_full)) 
                                               << 4U));
    vlSelfRef.__VvifTrigger_h65ecbd10__1_Vtrigm_full = 0U;
    vlSelfRef.__VactTriggered[1U] = ((0xfffffffffffffff7ULL 
                                      & vlSelfRef.__VactTriggered
                                      [1U]) | ((QData)((IData)(vlSelfRef.__VvifTrigger_h0e8631bc__2_Vtrigm_data)) 
                                               << 3U));
    vlSelfRef.__VvifTrigger_h0e8631bc__2_Vtrigm_data = 0U;
    vlSelfRef.__VactTriggered[1U] = ((0xfffffffffffffffbULL 
                                      & vlSelfRef.__VactTriggered
                                      [1U]) | ((QData)((IData)(vlSelfRef.__VvifTrigger_h0e8631bc__1_Vtrigm_empty)) 
                                               << 2U));
    vlSelfRef.__VvifTrigger_h0e8631bc__1_Vtrigm_empty = 0U;
    vlSelfRef.__VactTriggered[1U] = ((0xfffffffffffffffdULL 
                                      & vlSelfRef.__VactTriggered
                                      [1U]) | ((QData)((IData)(vlSelfRef.__VvifTrigger_h0e8631bc__0_Vtrigm_clk)) 
                                               << 1U));
    vlSelfRef.__VvifTrigger_h0e8631bc__0_Vtrigm_clk = 0U;
    vlSelfRef.__VactTriggered[1U] = ((0xfffffffffffffffeULL 
                                      & vlSelfRef.__VactTriggered
                                      [1U]) | (IData)((IData)(vlSelfRef.__VvifTrigger_h65ecbd10__0_Vtrigm_clk)));
    vlSelfRef.__VvifTrigger_h65ecbd10__0_Vtrigm_clk = 0U;
    __Vtrigprevexpr_hd86c879f__0 = (0U != vlSymsp->TOP__uvm_pkg__03a__03auvm_objection__Vclpkg.__PVT__m_scheduled_list.size());
    vlSelfRef.__VactTriggered[0U] = VL_EXTEND_QI(64,16, 
                                                 ((((IData)(__Vtrigprevexpr_hd86c879f__0) 
                                                    != (IData)(vlSelfRef.__Vtrigprevexpr_hd86c879f__1)) 
                                                   << 8U) 
                                                  | (((((((IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.start_clk) 
                                                          != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__start_clk__0)) 
                                                         << 3U) 
                                                        | (vlSelfRef.__VdlySched.awaitingCurrentTime() 
                                                           << 2U)) 
                                                       | ((vlSelfRef.__VdynSched.evaluate() 
                                                           << 1U) 
                                                          | ((IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.start_clk) 
                                                             != (IData)(vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__start_clk__0)))) 
                                                      << 4U) 
                                                     | (((((~ (IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.reset_n)) 
                                                           & (IData)(vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__reset_n__0)) 
                                                          << 3U) 
                                                         | (((IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.clk) 
                                                             & (~ (IData)(vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__clk__0))) 
                                                            << 2U)) 
                                                        | ((((~ (IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.reset_n)) 
                                                             & (IData)(vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__reset_n__0)) 
                                                            << 1U) 
                                                           | ((IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.clk) 
                                                              & (~ (IData)(vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__clk__0))))))));
    vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__clk__0 
        = vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.clk;
    vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__reset_n__0 
        = vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.reset_n;
    vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__clk__0 
        = vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.clk;
    vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__reset_n__0 
        = vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.reset_n;
    vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if__start_clk__0 
        = vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.start_clk;
    vlSelfRef.__Vtrigprevexpr___TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if__start_clk__0 
        = vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.start_clk;
    vlSelfRef.__Vtrigprevexpr_hd86c879f__1 = __Vtrigprevexpr_hd86c879f__0;
    if (VL_UNLIKELY(((1U & (~ (IData)(vlSelfRef.__VactDidInit)))))) {
        vlSelfRef.__VactDidInit = 1U;
        vlSelfRef.__VactTriggered[0U] = (0x0000000000000010ULL 
                                         | vlSelfRef.__VactTriggered
                                         [0U]);
        vlSelfRef.__VactTriggered[0U] = (0x0000000000000080ULL 
                                         | vlSelfRef.__VactTriggered
                                         [0U]);
        vlSelfRef.__VactTriggered[0U] = (0x0000000000000100ULL 
                                         | vlSelfRef.__VactTriggered
                                         [0U]);
    }
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        uvmt_fifo_tb___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
    }
#endif
    vlSelfRef.__VdynSched.doPostUpdates();
}

bool uvmt_fifo_tb___024root___trigger_anySet__act(const VlUnpacked<QData/*63:0*/, 2> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___trigger_anySet__act\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        if (in[n]) {
            return (1U);
        }
        n = ((IData)(1U) + n);
    } while ((2U > n));
    return (0U);
}

void uvmt_fifo_tb___024root___act_comb__TOP__0(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___act_comb__TOP__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    ([&]() {
            vlSelfRef.__VvifTrigger_h65ecbd10__0_Vtrigm_clk = 1U;
        }(), vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.clk) 
        = vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.clk;
}

void uvmt_fifo_tb___024root___act_comb__TOP__1(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___act_comb__TOP__1\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    ([&]() {
            vlSelfRef.__VvifTrigger_h0e8631bc__0_Vtrigm_clk = 1U;
        }(), vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.clk) 
        = vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.clk;
}

void uvmt_fifo_tb___024root___eval_act(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_act\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if ((0x0000000000000070ULL & vlSelfRef.__VactTriggered
         [0U])) {
        uvmt_fifo_tb___024root___act_comb__TOP__0(vlSelf);
    }
    if ((0x00000000000000e0ULL & vlSelfRef.__VactTriggered
         [0U])) {
        uvmt_fifo_tb___024root___act_comb__TOP__1(vlSelf);
    }
}

void uvmt_fifo_tb___024root___nba_sequent__TOP__0(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___nba_sequent__TOP__0\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__r_empty 
        = ((1U & (~ (IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.reset_n))) 
           || (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_empty_tmp));
    if (vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.reset_n) {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin 
            = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin_next;
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_o 
            = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_sync__DOT__ptr_temp;
    } else {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin = 0U;
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_o = 0U;
    }
    ([&]() {
            vlSelfRef.__VvifTrigger_h0e8631bc__1_Vtrigm_empty = 1U;
        }(), vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.empty) 
        = vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__r_empty;
    if (vlSymsp->TOP__uvmt_fifo_tb__DOT__rd_clk_gen_if.reset_n) {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_sync__DOT__ptr_temp 
            = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_i;
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_i 
            = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_gray_next;
    } else {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_sync__DOT__ptr_temp = 0U;
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_i = 0U;
    }
}

void uvmt_fifo_tb___024root___nba_sequent__TOP__1(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___nba_sequent__TOP__1\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__w_full 
        = ((IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.reset_n) 
           && (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_full_tmp));
    if (vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.reset_n) {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin 
            = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin_next;
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_o 
            = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_sync__DOT__ptr_temp;
    } else {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin = 0U;
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_o = 0U;
    }
    ([&]() {
            vlSelfRef.__VvifTrigger_h65ecbd10__1_Vtrigm_full = 1U;
        }(), vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.full) 
        = vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__w_full;
    if (vlSymsp->TOP__uvmt_fifo_tb__DOT__wr_clk_gen_if.reset_n) {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_sync__DOT__ptr_temp 
            = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_i;
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_i 
            = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_gray_next;
    } else {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_sync__DOT__ptr_temp = 0U;
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_ptr_i = 0U;
    }
}

void uvmt_fifo_tb___024root___nba_comb__TOP__2(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___nba_comb__TOP__2\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if (((IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.en) 
         & (~ (IData)(vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__w_full)))) {
        vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data[(0x0000000fU 
                                                                                & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin))] 
            = vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.data;
    }
}

void uvmt_fifo_tb___024root___nba_comb__TOP__4(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___nba_comb__TOP__4\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin_next 
        = (0x0000001fU & ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin) 
                          + (1U & ((~ (IData)(vlSelfRef.uvmt_fifo_tb__DOT____Vcellout__simple_demo_tb__w_full)) 
                                   & (IData)(vlSymsp->TOP__uvmt_fifo_tb__DOT__write_if.en)))));
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_gray_next 
        = (0x0000001fU & ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin_next) 
                          ^ VL_SHIFTR_III(5,5,32, (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_bin_next), 1U)));
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__r_ptr_gray_next 
        = ((0x00000018U & ((~ ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_o) 
                               >> 3U)) << 3U)) | (7U 
                                                  & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_ptr_o)));
    vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_full_tmp 
        = ((IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__w_ptr_gray_next) 
           == (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__w_full_checker__DOT__r_ptr_gray_next));
    ([&]() {
            vlSelfRef.__VvifTrigger_h0e8631bc__2_Vtrigm_data = 1U;
        }(), vlSymsp->TOP__uvmt_fifo_tb__DOT__read_if.data) 
        = vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__fifo_mem__DOT__fifo_data
        [(0x0000000fU & (IData)(vlSelfRef.uvmt_fifo_tb__DOT__simple_demo_tb__DOT__dut__DOT__r_empty_checker__DOT__r_ptr_bin))];
}

void uvmt_fifo_tb___024root___eval_nba(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_nba\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if ((0x0000000000000070ULL & vlSelfRef.__VnbaTriggered
         [0U])) {
        uvmt_fifo_tb___024root___act_comb__TOP__0(vlSelf);
    }
    if ((0x00000000000000e0ULL & vlSelfRef.__VnbaTriggered
         [0U])) {
        uvmt_fifo_tb___024root___act_comb__TOP__1(vlSelf);
    }
    if ((3ULL & vlSelfRef.__VnbaTriggered[0U])) {
        uvmt_fifo_tb___024root___nba_sequent__TOP__0(vlSelf);
        vlSelfRef.__Vm_traceActivity[3U] = 1U;
    }
    if ((0x000000000000000cULL & vlSelfRef.__VnbaTriggered
         [0U])) {
        uvmt_fifo_tb___024root___nba_sequent__TOP__1(vlSelf);
        vlSelfRef.__Vm_traceActivity[4U] = 1U;
    }
    if (((0x0000000000000011ULL & vlSelfRef.__VnbaTriggered
          [1U]) | (0x000000000000000cULL & vlSelfRef.__VnbaTriggered
                   [0U]))) {
        uvmt_fifo_tb___024root___nba_comb__TOP__2(vlSelf);
        vlSelfRef.__Vm_traceActivity[5U] = 1U;
    }
    if (((0x000000000000000eULL & vlSelfRef.__VnbaTriggered
          [1U]) | (0x000000000000000fULL & vlSelfRef.__VnbaTriggered
                   [0U]))) {
        uvmt_fifo_tb___024root___ico_comb__TOP__0(vlSelf);
    }
    if (((0x0000000000000011ULL & vlSelfRef.__VnbaTriggered
          [1U]) | (0x000000000000000fULL & vlSelfRef.__VnbaTriggered
                   [0U]))) {
        uvmt_fifo_tb___024root___nba_comb__TOP__4(vlSelf);
        vlSelfRef.__Vm_traceActivity[6U] = 1U;
    }
}

void uvmt_fifo_tb___024root___timing_commit(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___timing_commit\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if ((! (0x0000000000000010ULL & vlSelfRef.__VactTriggered
            [0U]))) {
        vlSelfRef.__VtrigSched_h4cdf0b8b__0.commit(
                                                   "@( uvmt_fifo_tb.wr_clk_gen_if.start_clk)");
    }
    if ((! (0x0000000000000080ULL & vlSelfRef.__VactTriggered
            [0U]))) {
        vlSelfRef.__VtrigSched_h2652d666__0.commit(
                                                   "@( uvmt_fifo_tb.rd_clk_gen_if.start_clk)");
    }
    if ((! (0x0000000000000100ULL & vlSelfRef.__VactTriggered
            [0U]))) {
        vlSelfRef.__VtrigSched_h505b55d0__0.commit(
                                                   "@( (32'sh0 != uvm_pkg::uvm_objection__Vclpkg.m_scheduled_list.size()))");
    }
}

void uvmt_fifo_tb___024root___timing_resume(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___timing_resume\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Body
    if ((0x0000000000000010ULL & vlSelfRef.__VactTriggered
         [0U])) {
        vlSelfRef.__VtrigSched_h4cdf0b8b__0.resume(
                                                   "@( uvmt_fifo_tb.wr_clk_gen_if.start_clk)");
    }
    if ((0x0000000000000020ULL & vlSelfRef.__VactTriggered
         [0U])) {
        vlSelfRef.__VdynSched.resume();
    }
    if ((0x0000000000000080ULL & vlSelfRef.__VactTriggered
         [0U])) {
        vlSelfRef.__VtrigSched_h2652d666__0.resume(
                                                   "@( uvmt_fifo_tb.rd_clk_gen_if.start_clk)");
    }
    if ((0x0000000000000100ULL & vlSelfRef.__VactTriggered
         [0U])) {
        vlSelfRef.__VtrigSched_h505b55d0__0.resume(
                                                   "@( (32'sh0 != uvm_pkg::uvm_objection__Vclpkg.m_scheduled_list.size()))");
    }
    if ((0x0000000000000040ULL & vlSelfRef.__VactTriggered
         [0U])) {
        vlSelfRef.__VdlySched.resume();
    }
}

void uvmt_fifo_tb___024root___trigger_orInto__act(VlUnpacked<QData/*63:0*/, 2> &out, const VlUnpacked<QData/*63:0*/, 2> &in) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___trigger_orInto__act\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        out[n] = (out[n] | in[n]);
        n = ((IData)(1U) + n);
    } while ((2U > n));
}

bool uvmt_fifo_tb___024root___eval_phase__act(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_phase__act\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VactExecute;
    // Body
    uvmt_fifo_tb___024root___eval_triggers__act(vlSelf);
    uvmt_fifo_tb___024root___timing_commit(vlSelf);
    uvmt_fifo_tb___024root___trigger_orInto__act(vlSelfRef.__VnbaTriggered, vlSelfRef.__VactTriggered);
    __VactExecute = uvmt_fifo_tb___024root___trigger_anySet__act(vlSelfRef.__VactTriggered);
    if (__VactExecute) {
        uvmt_fifo_tb___024root___timing_resume(vlSelf);
        uvmt_fifo_tb___024root___eval_act(vlSelf);
    }
    return (__VactExecute);
}

void uvmt_fifo_tb___024root___trigger_clear__act(VlUnpacked<QData/*63:0*/, 2> &out) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___trigger_clear__act\n"); );
    // Locals
    IData/*31:0*/ n;
    // Body
    n = 0U;
    do {
        out[n] = 0ULL;
        n = ((IData)(1U) + n);
    } while ((2U > n));
}

bool uvmt_fifo_tb___024root___eval_phase__nba(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_phase__nba\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = uvmt_fifo_tb___024root___trigger_anySet__act(vlSelfRef.__VnbaTriggered);
    if (__VnbaExecute) {
        uvmt_fifo_tb___024root___eval_nba(vlSelf);
        uvmt_fifo_tb___024root___trigger_clear__act(vlSelfRef.__VnbaTriggered);
    }
    if (vlSelfRef.__VnbaEventTrigger) {
        __VnbaExecute = 1U;
        vlSelfRef.__VnbaEventTrigger = 0U;
        vlSelfRef.__VnbaEvent.fire();
    }
    return (__VnbaExecute);
}

void uvmt_fifo_tb___024root___eval(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
    // Locals
    IData/*31:0*/ __VicoIterCount;
    IData/*31:0*/ __VnbaIterCount;
    // Body
    __VicoIterCount = 0U;
    vlSelfRef.__VicoFirstIteration = 1U;
    do {
        if (VL_UNLIKELY(((0x00000064U < __VicoIterCount)))) {
#ifdef VL_DEBUG
            uvmt_fifo_tb___024root___dump_triggers__ico(vlSelfRef.__VicoTriggered, "ico"s);
#endif
            VL_FATAL_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tb/uvmt_fifo_tb.sv", 12, "", "DIDNOTCONVERGE: Input combinational region did not converge after 100 tries");
        }
        __VicoIterCount = ((IData)(1U) + __VicoIterCount);
    } while (uvmt_fifo_tb___024root___eval_phase__ico(vlSelf));
    __VnbaIterCount = 0U;
    do {
        if (VL_UNLIKELY(((0x00000064U < __VnbaIterCount)))) {
#ifdef VL_DEBUG
            uvmt_fifo_tb___024root___dump_triggers__act(vlSelfRef.__VnbaTriggered, "nba"s);
#endif
            VL_FATAL_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tb/uvmt_fifo_tb.sv", 12, "", "DIDNOTCONVERGE: NBA region did not converge after 100 tries");
        }
        __VnbaIterCount = ((IData)(1U) + __VnbaIterCount);
        vlSelfRef.__VactIterCount = 0U;
        do {
            if (VL_UNLIKELY(((0x00000064U < vlSelfRef.__VactIterCount)))) {
#ifdef VL_DEBUG
                uvmt_fifo_tb___024root___dump_triggers__act(vlSelfRef.__VactTriggered, "act"s);
#endif
                VL_FATAL_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvmt/tb/uvmt_fifo_tb.sv", 12, "", "DIDNOTCONVERGE: Active region did not converge after 100 tries");
            }
            vlSelfRef.__VactIterCount = ((IData)(1U) 
                                         + vlSelfRef.__VactIterCount);
        } while (uvmt_fifo_tb___024root___eval_phase__act(vlSelf));
    } while (uvmt_fifo_tb___024root___eval_phase__nba(vlSelf));
}

#ifdef VL_DEBUG
void uvmt_fifo_tb___024root___eval_debug_assertions(uvmt_fifo_tb___024root* vlSelf) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    uvmt_fifo_tb___024root___eval_debug_assertions\n"); );
    uvmt_fifo_tb__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    auto& vlSelfRef = std::ref(*vlSelf).get();
}
#endif  // VL_DEBUG
