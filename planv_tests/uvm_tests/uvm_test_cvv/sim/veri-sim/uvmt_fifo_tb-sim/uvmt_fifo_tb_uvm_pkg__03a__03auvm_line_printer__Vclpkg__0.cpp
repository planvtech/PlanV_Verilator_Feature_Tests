// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi254> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi254> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi254__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvm_line_printer"s;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer__Vclpkg::__VnoInFunc_set_default(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer> printer) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer__Vclpkg::__VnoInFunc_set_default\n"); );
    // Body
    this->__PVT__m_default_line_printer = printer;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer__Vclpkg::__VnoInFunc_get_default(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer> &get_default__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer__Vclpkg::__VnoInFunc_get_default\n"); );
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    if ((VlNull{} == this->__PVT__m_default_line_printer)) {
        this->__PVT__m_default_line_printer = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer, vlProcess, vlSymsp, "uvm_default_line_printer"s);
    }
    get_default__Vfuncrtn = this->__PVT__m_default_line_printer;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi254> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi254__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer, vlProcess, vlSymsp, ""s)
            : VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_line_printer"s;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_tree_printer(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tree_printer::__PVT__m_newline = " "s;
    this->__VnoInFunc_set_indent(vlSymsp, 0U);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_set_separators(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string separators) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_set_separators\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_printer_knobs> __Vfunc_get_knobs__5__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__6__Vfuncout;
    __Vfunc_uvm_report_enabled__6__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__6__verbosity;
    __Vfunc_uvm_report_enabled__6__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__6__severity;
    __Vfunc_uvm_report_enabled__6__severity = 0;
    std::string __Vfunc_uvm_report_enabled__6__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__7__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__8__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__9__Vfuncout;
    __Vtask_uvm_report_enabled__9__Vfuncout = 0;
    std::string __Vtask_uvm_report_error__10__id;
    std::string __Vtask_uvm_report_error__10__message;
    IData/*31:0*/ __Vtask_uvm_report_error__10__verbosity;
    __Vtask_uvm_report_error__10__verbosity = 0;
    std::string __Vtask_uvm_report_error__10__filename;
    IData/*31:0*/ __Vtask_uvm_report_error__10__line;
    __Vtask_uvm_report_error__10__line = 0;
    std::string __Vtask_uvm_report_error__10__context_name;
    CData/*0:0*/ __Vtask_uvm_report_error__10__report_enabled_checked;
    __Vtask_uvm_report_error__10__report_enabled_checked = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__11__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__12__Vfuncout;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_printer_knobs> _knobs;
    this->__VnoInFunc_get_knobs(vlSymsp, __Vfunc_get_knobs__5__Vfuncout);
    _knobs = __Vfunc_get_knobs__5__Vfuncout;
    if (VL_GTS_III(32, 2U, VL_LEN_IN(separators))) {
        if ((0U != ([&]() {
                        __Vfunc_uvm_report_enabled__6__id = "UVM/PRINT/SHORT_SEP"s;
                        __Vfunc_uvm_report_enabled__6__severity = 2U;
                        __Vfunc_uvm_report_enabled__6__verbosity = 0U;
                        vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__7__Vfuncout);
                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                            = __Vfunc_get__7__Vfuncout;
                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                    ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__8__Vfuncout);
                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                            = __Vtask_get_root__8__Vfuncout;
                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                    ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__6__verbosity, (IData)(__Vfunc_uvm_report_enabled__6__severity), __Vfunc_uvm_report_enabled__6__id, __Vtask_uvm_report_enabled__9__Vfuncout);
                        __Vfunc_uvm_report_enabled__6__Vfuncout 
                            = __Vtask_uvm_report_enabled__9__Vfuncout;
                    }(), __Vfunc_uvm_report_enabled__6__Vfuncout))) {
            __Vtask_uvm_report_error__10__report_enabled_checked = 1U;
            __Vtask_uvm_report_error__10__context_name = ""s;
            __Vtask_uvm_report_error__10__line = 0x00000760U;
            __Vtask_uvm_report_error__10__filename = "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_printer.svh"s;
            __Vtask_uvm_report_error__10__verbosity = 0U;
            __Vtask_uvm_report_error__10__message = VL_SFORMATF_N_NX("Bad call: set_separators(%@) (Argument must have at least 2 characters)",0,
                                                                     -1,
                                                                     &(separators)) ;
            __Vtask_uvm_report_error__10__id = "UVM/PRINT/SHORT_SEP"s;
            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__11__Vfuncout);
            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_error__Vstatic__cs 
                = __Vfunc_get__11__Vfuncout;
            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_error__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 174)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__12__Vfuncout);
            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_error__Vstatic__top 
                = __Vtask_get_root__12__Vfuncout;
            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_error__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 175)->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, __Vtask_uvm_report_error__10__id, __Vtask_uvm_report_error__10__message, __Vtask_uvm_report_error__10__verbosity, __Vtask_uvm_report_error__10__filename, __Vtask_uvm_report_error__10__line, __Vtask_uvm_report_error__10__context_name, (IData)(__Vtask_uvm_report_error__10__report_enabled_checked));
        }
    }
    VL_NULL_CHECK(_knobs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_printer.svh", 1890)->__PVT__separator 
        = separators;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_get_separators(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_separators__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_get_separators\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_printer_knobs> __Vfunc_get_knobs__14__Vfuncout;
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_printer_knobs> _knobs;
    this->__VnoInFunc_get_knobs(vlSymsp, __Vfunc_get_knobs__14__Vfuncout);
    _knobs = __Vfunc_get_knobs__14__Vfuncout;
    get_separators__Vfuncrtn = VL_NULL_CHECK(_knobs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_printer.svh", 1894)
        ->__PVT__separator;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_flush(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_flush\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_tree_printer::__VnoInFunc_flush(vlProcess, vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__17__Vfuncout;
    __Vfunc___VBasicRand__17__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__17__Vfuncout);
            }(), __Vfunc___VBasicRand__17__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_line_printer::to_string_middle\n"); );
    // Body
    std::string out;
    out += uvmt_fifo_tb_uvm_pkg__03a__03auvm_tree_printer::to_string_middle();
    return (out);
}
