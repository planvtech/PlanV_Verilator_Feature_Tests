// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_send_request(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> request, CData/*0:0*/ rerandomize) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_send_request\n"); );
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> m_request;
    if ((VlNull{} == uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer)) {
        this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "SSENDREQ"s, "Null m_sequencer reference"s, 0U, ""s, 0U, ""s, 0U);
    }
    if ((1U & (~ (0U != ([&]() {
                            m_request = request;
                        }(), 1U))))) {
        this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "SSENDREQ"s, "Failure to cast uvm_sequence_item to request"s, 0U, ""s, 0U, ""s, 0U);
    }
    VL_NULL_CHECK(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequence.svh", 83)->__VnoInFunc_send_request(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_>{this}, m_request, rerandomize);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_get_current_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &get_current_item__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_get_current_item\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_get_current_item__5__Vfuncout;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    if ((! VL_CAST_DYNAMIC(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__PVT__m_sequencer, this->__PVT__param_sequencer))) {
        this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "SGTCURR"s, "Failure to cast m_sequencer to the parameterized sequencer"s, 0U, ""s, 0U, ""s, 0U);
    }
    VL_NULL_CHECK(this->__PVT__param_sequencer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequence.svh", 102)->__VnoInFunc_get_current_item(vlSymsp, __Vtask_get_current_item__5__Vfuncout);
    get_current_item__Vfuncrtn = __Vtask_get_current_item__5__Vfuncout;
}

VlCoroutine uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_get_response(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &response, IData/*31:0*/ transaction_id) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_get_response\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> __Vtask_get_base_response__6__response;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    VL_KEEP_THIS;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> rsp;
    co_await this->__VnoInFunc_get_base_response(vlProcess, vlSymsp, __Vtask_get_base_response__6__response, transaction_id);
    rsp = __Vtask_get_base_response__6__response;
    if (VL_UNLIKELY(((1U & (~ (0U != ([&]() {
                                    response = rsp;
                                }(), 1U))))))) {
        VL_WRITEF_NX("[%0t] %%Error: uvm_sequence.svh:128: Assertion failed in %Nuvm_pkg.uvm_sequence_.get_response: '$cast' failed.\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9,vlSymsp->name());
        VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequence.svh", 128, "");
    }
    co_return;}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_put_response(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> response_item) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_put_response\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> response;
    if ((1U & (~ (0U != ([&]() {
                            response = response_item;
                        }(), 1U))))) {
        this->__VnoInFunc_uvm_report_fatal(vlProcess, vlSymsp, "PUTRSP"s, "Failure to cast response in put_response"s, 0U, ""s, 0U, ""s, 0U);
    }
    this->__VnoInFunc_put_base_response(vlProcess, vlSymsp, response_item);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_do_print\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item::__VnoInFunc_do_print(vlProcess, vlSymsp, printer);
    VL_NULL_CHECK(printer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequence.svh", 150)->__VnoInFunc_print_object(vlProcess, vlSymsp, "req"s, this->__PVT__req, 0x2eU);
    VL_NULL_CHECK(printer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/seq/uvm_sequence.svh", 151)->__VnoInFunc_print_object(vlProcess, vlSymsp, "rsp"s, this->__PVT__rsp, 0x2eU);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__13__Vfuncout;
    __Vfunc___VBasicRand__13__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__13__Vfuncout);
            }(), __Vfunc___VBasicRand__13__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_::to_string_middle\n"); );
    // Body
    std::string out;
    out += "param_sequencer:" + VL_TO_STRING(__PVT__param_sequencer);
    out += ", req:" + VL_TO_STRING(__PVT__req);
    out += ", rsp:" + VL_TO_STRING(__PVT__rsp);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base::to_string_middle();
    return (out);
}
