// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz480> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz480> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__Tz480__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz480> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__Tz480__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442, vlProcess, vlSymsp, "uvm_reg_sequence_inst"s)
            : VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence__Tz353_TBz353(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    this->__PVT__parent_select = 0U;
    ;
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_body(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_body\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__4__Vfuncout;
    __Vfunc_uvm_report_enabled__4__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__6__Vfuncout;
    __Vfunc_uvm_report_enabled__6__Vfuncout = 0;
    std::string __Vtask_get_full_name__8__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__9__Vfuncout;
    __Vfunc_uvm_report_enabled__9__Vfuncout = 0;
    std::string __Vtask_get_full_name__11__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> __Vtask_peek__12__t;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> __Vtask_get__14__t;
    // Body
    VL_KEEP_THIS;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> unnamedblk1__DOT__reg_item;
    if ((VlNull{} == uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "NO_SEQR"s, __Vfunc_uvm_report_enabled__4__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__4__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "NO_SEQR"s, "Sequence executing as translation sequence, but is not associated with a sequencer (m_sequencer == null)"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x00000083U, ""s, 1U);
        }
    }
    if ((VlNull{} == this->__PVT__reg_seqr)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 1U, "REG_XLATE_NO_SEQR"s, __Vfunc_uvm_report_enabled__6__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__6__Vfuncout))) {
            this->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, "REG_XLATE_NO_SEQR"s, 
                                                 VL_CVT_PACK_STR_NN(
                                                                    VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Executing RegModel translation sequence on sequencer "s, 
                                                                                ([&]() {
                                        VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 137)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__8__Vfuncout);
                                    }(), __Vtask_get_full_name__8__Vfuncout)), "' does not have an upstream sequencer defined. "s), "Execution of register items available only via direct calls to 'do_reg_item'"s)), 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x00000089U, ""s, 1U);
        }
        co_await VlForever{};
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x00000064U, 0U, "REG_XLATE_SEQ_START"s, __Vfunc_uvm_report_enabled__9__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__9__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "REG_XLATE_SEQ_START"s, 
                                          VL_CVT_PACK_STR_NN(
                                                             VL_CONCATN_NNN(
                                                                            VL_CONCATN_NNN("Starting RegModel translation sequence on sequencer "s, 
                                                                                ([&]() {
                                VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 142)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__11__Vfuncout);
                            }(), __Vtask_get_full_name__11__Vfuncout)), "'"s)), 0x00000064U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x0000008eU, ""s, 1U);
    }
    while (true) {
        co_await VL_NULL_CHECK(this->__PVT__reg_seqr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 145)->__VnoInFunc_peek(vlProcess, vlSymsp, __Vtask_peek__12__t);
        unnamedblk1__DOT__reg_item = __Vtask_peek__12__t;
        co_await this->__VnoInFunc_do_reg_item(vlProcess, vlSymsp, unnamedblk1__DOT__reg_item);
        co_await VL_NULL_CHECK(this->__PVT__reg_seqr, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 147)->__VnoInFunc_get(vlProcess, vlSymsp, __Vtask_get__14__t);
        unnamedblk1__DOT__reg_item = __Vtask_get__14__t;
        co_await vlSymsp->TOP.__VdlySched.delay(0ULL, 
                                                vlProcess, 
                                                "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 
                                                148);
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_do_reg_item(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_item> rw) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_do_reg_item\n"); );
    // Locals
    std::string __Vtask_convert2string__15__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__16__Vfuncout;
    __Vfunc_uvm_report_enabled__16__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__18__Vfuncout;
    __Vfunc_uvm_report_enabled__18__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__20__Vfuncout;
    __Vfunc_uvm_report_enabled__20__Vfuncout = 0;
    // Body
    VL_KEEP_THIS;
    std::string rws;
    VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 163)->__VnoInFunc_convert2string(vlProcess, vlSymsp, __Vtask_convert2string__15__Vfuncout);
    rws = __Vtask_convert2string__15__Vfuncout;
    if ((VlNull{} == uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "REG/DO_ITEM/NULL"s, __Vfunc_uvm_report_enabled__16__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__16__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "REG/DO_ITEM/NULL"s, "do_reg_item: m_sequencer is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x000000a5U, ""s, 1U);
        }
    }
    if ((VlNull{} == this->__PVT__adapter)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 3U, "REG/DO_ITEM/NULL"s, __Vfunc_uvm_report_enabled__18__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__18__Vfuncout))) {
            this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "REG/DO_ITEM/NULL"s, "do_reg_item: adapter handle is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x000000a7U, ""s, 1U);
        }
    }
    if ((0U != ([&]() {
                    this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0x0000012cU, 0U, "DO_RW_ACCESS"s, __Vfunc_uvm_report_enabled__20__Vfuncout);
                }(), __Vfunc_uvm_report_enabled__20__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, "DO_RW_ACCESS"s, 
                                          VL_CVT_PACK_STR_NN(
                                                             VL_CONCATN_NNN("Doing transaction: "s, rws)), 0x0000012cU, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x000000a9U, ""s, 1U);
    }
    if ((0U == this->__PVT__parent_select)) {
        this->__PVT__upstream_parent = VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 172)
            ->__PVT__parent;
        VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 173)->__PVT__parent 
            = VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this};
    }
    if ((1U == VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 176)
         ->__PVT__kind)) {
        co_await VL_NULL_CHECK(VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 177)
                               ->__PVT__local_map, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 177)->__VnoInFunc_do_bus_write(vlProcess, vlSymsp, rw, uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer, this->__PVT__adapter);
    } else {
        co_await VL_NULL_CHECK(VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 179)
                               ->__PVT__local_map, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 179)->__VnoInFunc_do_bus_read(vlProcess, vlSymsp, rw, uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer, this->__PVT__adapter);
    }
    if ((0U == this->__PVT__parent_select)) {
        VL_NULL_CHECK(rw, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 182)->__PVT__parent 
            = this->__PVT__upstream_parent;
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_write_reg(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> rg, IData/*31:0*/ &status, QData/*63:0*/ value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_write_reg\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__24__Vfuncout;
    __Vfunc_uvm_report_enabled__24__Vfuncout = 0;
    IData/*31:0*/ __Vtask_write__26__status;
    __Vtask_write__26__status = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((VlNull{} == rg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_REG"s, __Vfunc_uvm_report_enabled__24__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__24__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_REG"s, "Register argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x000000d7U, ""s, 1U);
        }
    } else {
        co_await VL_NULL_CHECK(rg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 217)->__VnoInFunc_write(vlProcess, vlSymsp, __Vtask_write__26__status, value, path, map, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, prior, extension, fname, lineno);
        status = __Vtask_write__26__status;
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_read_reg(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> rg, IData/*31:0*/ &status, QData/*63:0*/ &value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_read_reg\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__27__Vfuncout;
    __Vfunc_uvm_report_enabled__27__Vfuncout = 0;
    IData/*31:0*/ __Vtask_read__29__status;
    __Vtask_read__29__status = 0;
    QData/*63:0*/ __Vtask_read__29__value;
    __Vtask_read__29__value = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((VlNull{} == rg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_REG"s, __Vfunc_uvm_report_enabled__27__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__27__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_REG"s, "Register argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x000000e9U, ""s, 1U);
        }
    } else {
        co_await VL_NULL_CHECK(rg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 235)->__VnoInFunc_read(vlProcess, vlSymsp, __Vtask_read__29__status, __Vtask_read__29__value, path, map, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, prior, extension, fname, lineno);
        status = __Vtask_read__29__status;
        value = __Vtask_read__29__value;
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_poke_reg(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> rg, IData/*31:0*/ &status, QData/*63:0*/ value, std::string kind, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_poke_reg\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__30__Vfuncout;
    __Vfunc_uvm_report_enabled__30__Vfuncout = 0;
    IData/*31:0*/ __Vtask_poke__32__status;
    __Vtask_poke__32__status = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((VlNull{} == rg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_REG"s, __Vfunc_uvm_report_enabled__30__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__30__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_REG"s, "Register argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x000000faU, ""s, 1U);
        }
    } else {
        co_await VL_NULL_CHECK(rg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 252)->__VnoInFunc_poke(vlSymsp, __Vtask_poke__32__status, value, kind, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, extension, fname, lineno);
        status = __Vtask_poke__32__status;
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_peek_reg(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> rg, IData/*31:0*/ &status, QData/*63:0*/ &value, std::string kind, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_peek_reg\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__33__Vfuncout;
    __Vfunc_uvm_report_enabled__33__Vfuncout = 0;
    IData/*31:0*/ __Vtask_peek__35__status;
    __Vtask_peek__35__status = 0;
    QData/*63:0*/ __Vtask_peek__35__value;
    __Vtask_peek__35__value = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((VlNull{} == rg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_REG"s, __Vfunc_uvm_report_enabled__33__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__33__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_REG"s, "Register argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x0000010bU, ""s, 1U);
        }
    } else {
        co_await VL_NULL_CHECK(rg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 269)->__VnoInFunc_peek(vlSymsp, __Vtask_peek__35__status, __Vtask_peek__35__value, kind, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, extension, fname, lineno);
        status = __Vtask_peek__35__status;
        value = __Vtask_peek__35__value;
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_update_reg(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> rg, IData/*31:0*/ &status, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_update_reg\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__36__Vfuncout;
    __Vfunc_uvm_report_enabled__36__Vfuncout = 0;
    IData/*31:0*/ __Vtask_update__38__status;
    __Vtask_update__38__status = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((VlNull{} == rg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_REG"s, __Vfunc_uvm_report_enabled__36__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__36__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_REG"s, "Register argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x0000011dU, ""s, 1U);
        }
    } else {
        co_await VL_NULL_CHECK(rg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 287)->__VnoInFunc_update(vlSymsp, __Vtask_update__38__status, path, map, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, prior, extension, fname, lineno);
        status = __Vtask_update__38__status;
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_mirror_reg(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg> rg, IData/*31:0*/ &status, IData/*31:0*/ check, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_mirror_reg\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__39__Vfuncout;
    __Vfunc_uvm_report_enabled__39__Vfuncout = 0;
    IData/*31:0*/ __Vtask_mirror__41__status;
    __Vtask_mirror__41__status = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((VlNull{} == rg)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_REG"s, __Vfunc_uvm_report_enabled__39__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__39__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_REG"s, "Register argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x00000130U, ""s, 1U);
        }
    } else {
        co_await VL_NULL_CHECK(rg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 306)->__VnoInFunc_mirror(vlProcess, vlSymsp, __Vtask_mirror__41__status, check, path, map, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, prior, extension, fname, lineno);
        status = __Vtask_mirror__41__status;
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_write_mem(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> mem, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_write_mem\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__42__Vfuncout;
    __Vfunc_uvm_report_enabled__42__Vfuncout = 0;
    IData/*31:0*/ __Vtask_write__44__status;
    __Vtask_write__44__status = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((VlNull{} == mem)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_MEM"s, __Vfunc_uvm_report_enabled__42__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__42__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_MEM"s, "Memory argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x00000144U, ""s, 1U);
        }
    } else {
        co_await VL_NULL_CHECK(mem, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 326)->__VnoInFunc_write(vlProcess, vlSymsp, __Vtask_write__44__status, offset, value, path, map, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, prior, extension, fname, lineno);
        status = __Vtask_write__44__status;
    }
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_read_mem(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> mem, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ &value, IData/*31:0*/ path, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_map> map, IData/*31:0*/ prior, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_read_mem\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__45__Vfuncout;
    __Vfunc_uvm_report_enabled__45__Vfuncout = 0;
    IData/*31:0*/ __Vtask_read__47__status;
    __Vtask_read__47__status = 0;
    QData/*63:0*/ __Vtask_read__47__value;
    __Vtask_read__47__value = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((VlNull{} == mem)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_MEM"s, __Vfunc_uvm_report_enabled__45__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__45__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_MEM"s, "Memory argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x00000157U, ""s, 1U);
        }
    } else {
        co_await VL_NULL_CHECK(mem, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 345)->__VnoInFunc_read(vlProcess, vlSymsp, __Vtask_read__47__status, offset, __Vtask_read__47__value, path, map, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, prior, extension, fname, lineno);
        status = __Vtask_read__47__status;
        value = __Vtask_read__47__value;
    }
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_poke_mem(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> mem, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ value, std::string kind, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_poke_mem\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__48__Vfuncout;
    __Vfunc_uvm_report_enabled__48__Vfuncout = 0;
    IData/*31:0*/ __Vtask_poke__50__status;
    __Vtask_poke__50__status = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    if ((VlNull{} == mem)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_MEM"s, __Vfunc_uvm_report_enabled__48__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__48__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_MEM"s, "Memory argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x00000169U, ""s, 1U);
        }
    } else {
        VL_NULL_CHECK(mem, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 363)->__VnoInFunc_poke(vlProcess, vlSymsp, __Vtask_poke__50__status, offset, value, kind, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, extension, fname, lineno);
        status = __Vtask_poke__50__status;
    }
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_peek_mem(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_mem> mem, IData/*31:0*/ &status, QData/*63:0*/ offset, QData/*63:0*/ &value, std::string kind, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> extension, std::string fname, IData/*31:0*/ lineno) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_peek_mem\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_uvm_report_enabled__51__Vfuncout;
    __Vfunc_uvm_report_enabled__51__Vfuncout = 0;
    IData/*31:0*/ __Vtask_peek__53__status;
    __Vtask_peek__53__status = 0;
    QData/*63:0*/ __Vtask_peek__53__value;
    __Vtask_peek__53__value = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    if ((VlNull{} == mem)) {
        if ((0U != ([&]() {
                        this->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, 0U, 2U, "NO_MEM"s, __Vfunc_uvm_report_enabled__51__Vfuncout);
                    }(), __Vfunc_uvm_report_enabled__51__Vfuncout))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "NO_MEM"s, "Memory argument is null"s, 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh"s, 0x0000017bU, ""s, 1U);
        }
    } else {
        VL_NULL_CHECK(mem, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/reg/uvm_reg_sequence.svh", 381)->__VnoInFunc_peek(vlProcess, vlSymsp, __Vtask_peek__53__status, offset, __Vtask_peek__53__value, kind, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>{this}, extension, fname, lineno);
        status = __Vtask_peek__53__status;
        value = __Vtask_peek__53__value;
    }
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_put_response(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> response_item) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_put_response\n"); );
    // Body
    this->__VnoInFunc_put_base_response(vlProcess, vlSymsp, response_item);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__56__Vfuncout;
    __Vfunc___VBasicRand__56__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__56__Vfuncout);
            }(), __Vfunc___VBasicRand__56__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__parent_select = 0;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_reg_sequence__Tz442::to_string_middle\n"); );
    // Body
    std::string out;
    out += "model:" + VL_TO_STRING(__PVT__model);
    out += ", adapter:" + VL_TO_STRING(__PVT__adapter);
    out += ", reg_seqr:" + VL_TO_STRING(__PVT__reg_seqr);
    out += ", parent_select:" + VL_TO_STRING(__PVT__parent_select);
    out += ", upstream_parent:" + VL_TO_STRING(__PVT__upstream_parent);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence__Tz353_TBz353::to_string_middle();
    return (out);
}
