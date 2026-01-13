// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer___Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__Tz207> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer___Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__Tz207> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__Tz207__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component_registry__Tz207> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_component_registry__Tz207__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_item_done_get_trigger_data(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &item_done_get_trigger_data__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_item_done_get_trigger_data\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vfunc_last_rsp__1__Vfuncout;
    // Body
    this->__VnoInFunc_last_rsp(vlSymsp, 0U, __Vfunc_last_rsp__1__Vfuncout);
    item_done_get_trigger_data__Vfuncrtn = __Vfunc_last_rsp__1__Vfuncout;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base_(vlProcess, vlSymsp, name, parent) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    this->__PVT__seq_item_export = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_seq_item_pull_imp__pi104, vlProcess, vlSymsp, "seq_item_export"s, 
                                          VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_>{this});
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_stop_sequences(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_stop_sequences\n"); );
    // Locals
    IData/*31:0*/ __Vtask_used__5__Vfuncout;
    __Vtask_used__5__Vfuncout = 0;
    std::string __Vfunc_get_full_name__7__Vfuncout;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base::__VnoInFunc_stop_sequences(vlSymsp);
    this->__PVT__sequence_item_requested = 0U;
    this->__PVT__get_next_item_called = 0U;
    if ((0U != ([&]() {
                    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base_::__PVT__m_req_fifo, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 173)
                ->__VnoInFunc_used(vlSymsp, __Vtask_used__5__Vfuncout);
                }(), __Vtask_used__5__Vfuncout))) {
        this->__VnoInFunc_uvm_report_info(vlProcess, vlSymsp, 
                                          VL_CVT_PACK_STR_NN(
                                                             ([&]() {
                        this->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vfunc_get_full_name__7__Vfuncout);
                    }(), __Vfunc_get_full_name__7__Vfuncout)), "Sequences stopped.  Removing request from sequencer fifo"s, 0x000000c8U, ""s, 0U, ""s, 0U);
        VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base_::__PVT__m_req_fifo, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 175)->__VnoInFunc_flush(vlSymsp);
    }
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_sequencer"s;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_m_find_number_driver_connections(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &m_find_number_driver_connections__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_m_find_number_driver_connections\n"); );
    // Body
    VlAssocArray<std::string, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_port_base__Tz208>> provided_to_port_list;
    VL_NULL_CHECK(this->__PVT__seq_item_export, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 200)->__VnoInFunc_get_provided_to(vlSymsp, provided_to_port_list);
    m_find_number_driver_connections__Vfuncrtn = provided_to_port_list.size();
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_get_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_get_next_item\n"); );
    // Locals
    std::string __Vfunc_get_full_name__11__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_peek__13__t;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> req_item;
    if (this->__PVT__get_next_item_called) {
        this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, 
                                           VL_CVT_PACK_STR_NN(
                                                              ([&]() {
                        this->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vfunc_get_full_name__11__Vfuncout);
                    }(), __Vfunc_get_full_name__11__Vfuncout)), "Get_next_item called twice without item_done or get in between"s, 0U, ""s, 0U, ""s, 0U);
    }
    if ((1U & (~ (IData)(this->__PVT__sequence_item_requested)))) {
        co_await this->__VnoInFunc_m_select_sequence(vlProcess, vlSymsp);
    }
    this->__PVT__sequence_item_requested = 1U;
    this->__PVT__get_next_item_called = 1U;
    co_await VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base_::__PVT__m_req_fifo, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 225)->__VnoInFunc_peek(vlSymsp, __Vtask_peek__13__t);
    t = __Vtask_peek__13__t;
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_try_next_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_try_next_item\n"); );
    // Locals
    std::string __Vfunc_get_full_name__15__Vfuncout;
    IData/*31:0*/ __Vfunc_m_choose_next_request__17__Vfuncout;
    __Vfunc_m_choose_next_request__17__Vfuncout = 0;
    CData/*0:0*/ __Vtask_try_peek__21__Vfuncout;
    __Vtask_try_peek__21__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_try_peek__21__t;
    std::string __Vtask_get_full_name__23__Vfuncout;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    IData/*31:0*/ selected_sequence;
    selected_sequence = 0;
    QData/*63:0*/ arb_time;
    arb_time = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> seq;
    {
        if (this->__PVT__get_next_item_called) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, 
                                               VL_CVT_PACK_STR_NN(
                                                                  ([&]() {
                            this->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vfunc_get_full_name__15__Vfuncout);
                        }(), __Vfunc_get_full_name__15__Vfuncout)), "get_next_item/try_next_item called twice without item_done or get in between"s, 0U, ""s, 0U, ""s, 0U);
            goto __Vlabel0;
        }
        co_await this->__VnoInFunc_wait_for_sequences(vlProcess, vlSymsp);
        this->__VnoInFunc_m_choose_next_request(vlProcess, vlSymsp, __Vfunc_m_choose_next_request__17__Vfuncout);
        selected_sequence = __Vfunc_m_choose_next_request__17__Vfuncout;
        if ((0xffffffffU == selected_sequence)) {
            t = VlNull{};
            goto __Vlabel0;
        }
        this->__VnoInFunc_m_set_arbitration_completed(vlSymsp, VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base::__PVT__arb_sequence_q.at(selected_sequence), "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 256)
                                                      ->__PVT__request_id);
        seq = VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base::__PVT__arb_sequence_q.at(selected_sequence), "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 257)
            ->__PVT__sequence_ptr;
        uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base::__PVT__arb_sequence_q.erase(selected_sequence);
        this->__VnoInFunc_m_update_lists(vlSymsp);
        this->__PVT__sequence_item_requested = 1U;
        this->__PVT__get_next_item_called = 1U;
        co_await this->__VnoInFunc_wait_for_sequences(vlProcess, vlSymsp);
        if ((1U & (~ ([&]() {
                            VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base_::__PVT__m_req_fifo, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 267)
                      ->__VnoInFunc_try_peek(vlSymsp, __Vtask_try_peek__21__t, __Vtask_try_peek__21__Vfuncout);
                            t = __Vtask_try_peek__21__t;
                        }(), (IData)(__Vtask_try_peek__21__Vfuncout))))) {
            this->__VnoInFunc_uvm_report_error(vlProcess, vlSymsp, "TRY_NEXT_BLOCKED"s, 
                                               VL_CVT_PACK_STR_NN(
                                                                  VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("try_next_item: the selected sequence '"s, 
                                                                                ([&]() {
                                            VL_NULL_CHECK(seq, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 269)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__23__Vfuncout);
                                        }(), __Vtask_get_full_name__23__Vfuncout)), "' did not produce an item within an NBA delay. "s), "Sequences should not consume time between calls to start_item and finish_item. "s), "Returning null item."s)), 0U, ""s, 0U, ""s, 0U);
        }
        __Vlabel0: ;
    }
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_item_done(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> item) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_item_done\n"); );
    // Locals
    CData/*0:0*/ __Vtask_try_get__24__Vfuncout;
    __Vtask_try_get__24__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_try_get__24__t;
    IData/*31:0*/ __Vtask_get_sequence_id__25__Vfuncout;
    __Vtask_get_sequence_id__25__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_transaction_id__26__Vfuncout;
    __Vtask_get_transaction_id__26__Vfuncout = 0;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t;
    this->__PVT__sequence_item_requested = 0U;
    this->__PVT__get_next_item_called = 0U;
    if (([&]() {
                VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base_::__PVT__m_req_fifo, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 286)
         ->__VnoInFunc_try_get(vlSymsp, __Vtask_try_get__24__t, __Vtask_try_get__24__Vfuncout);
                t = __Vtask_try_get__24__t;
            }(), (IData)(__Vtask_try_get__24__Vfuncout))) {
        VL_NULL_CHECK(t, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 290)->__VnoInFunc_get_sequence_id(vlSymsp, __Vtask_get_sequence_id__25__Vfuncout);
        uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base::__PVT__m_wait_for_item_sequence_id 
            = __Vtask_get_sequence_id__25__Vfuncout;
        VL_NULL_CHECK(t, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 291)->__VnoInFunc_get_transaction_id(vlSymsp, __Vtask_get_transaction_id__26__Vfuncout);
        uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base::__PVT__m_wait_for_item_transaction_id 
            = __Vtask_get_transaction_id__26__Vfuncout;
    } else {
        this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "SQRBADITMDN"s, "Item_done() called with no outstanding requests. Each call to item_done() must be paired with a previous call to get_next_item()."s, 0U, ""s, 0U, ""s, 0U);
    }
    if ((VlNull{} != item)) {
        VL_NULL_CHECK(this->__PVT__seq_item_export, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 295)->__VnoInFunc_put_response(vlSymsp, item);
    }
    this->__VnoInFunc_grant_queued_locks(vlProcess, vlSymsp);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_put(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_put\n"); );
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    this->__VnoInFunc_put_response(vlProcess, vlSymsp, t);
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_get\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_peek__32__t;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((1U & (~ (IData)(this->__PVT__sequence_item_requested)))) {
        co_await this->__VnoInFunc_m_select_sequence(vlProcess, vlSymsp);
    }
    this->__PVT__sequence_item_requested = 1U;
    co_await VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base_::__PVT__m_req_fifo, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 319)->__VnoInFunc_peek(vlSymsp, __Vtask_peek__32__t);
    t = __Vtask_peek__32__t;
    this->__VnoInFunc_item_done(vlSymsp, VlNull{});
    co_return;}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_peek(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &t) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_peek\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_peek__35__t;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    if ((1U & (~ (IData)(this->__PVT__sequence_item_requested)))) {
        co_await this->__VnoInFunc_m_select_sequence(vlProcess, vlSymsp);
    }
    this->__PVT__sequence_item_requested = 1U;
    co_await VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base_::__PVT__m_req_fifo, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequencer.svh", 336)->__VnoInFunc_peek(vlSymsp, __Vtask_peek__35__t);
    t = __Vtask_peek__35__t;
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_item_done_trigger(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> item) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_item_done_trigger\n"); );
    // Body
    this->__VnoInFunc_item_done(vlSymsp, item);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__38__Vfuncout;
    __Vfunc___VBasicRand__38__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__38__Vfuncout);
            }(), __Vfunc___VBasicRand__38__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__sequence_item_requested = 0;
    __PVT__get_next_item_called = 0;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_::to_string_middle\n"); );
    // Body
    std::string out;
    out += "sequence_item_requested:" + VL_TO_STRING(__PVT__sequence_item_requested);
    out += ", get_next_item_called:" + VL_TO_STRING(__PVT__get_next_item_called);
    out += ", seq_item_export:" + VL_TO_STRING(__PVT__seq_item_export);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_param_base_::to_string_middle();
    return (out);
}
