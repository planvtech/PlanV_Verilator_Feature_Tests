// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_get_value(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &get_value__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_get_value\n"); );
    // Body
    get_value__Vfuncrtn = this->__PVT___val;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_set_value(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> value) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_set_value\n"); );
    // Body
    this->__PVT___val = value;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_do_print\n"); );
    // Body
    VL_NULL_CHECK(printer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_report_message.svh", 258)->__VnoInFunc_print_object(vlProcess, vlSymsp, uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base::__PVT___name, this->__PVT___val, 0x2eU);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_do_record(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> recorder) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_do_record\n"); );
    // Body
    VL_NULL_CHECK(recorder, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_report_message.svh", 262)->__VnoInFunc_record_object(vlProcess, vlSymsp, uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base::__PVT___name, this->__PVT___val);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_do_copy(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base> rhs) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_do_copy\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element> _rhs;
    if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(rhs, _rhs))))) {
        VL_WRITEF_NX("[%0t] %%Error: uvm_report_message.svh:267: Assertion failed in %Nuvm_pkg.uvm_report_message_object_element.do_copy: '$cast' failed.\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9,vlSymsp->name());
        VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_report_message.svh", 267, "");
    }
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base::__PVT___name 
        = VL_NULL_CHECK(_rhs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_report_message.svh", 268)
        ->__PVT___name;
    this->__PVT___val = VL_NULL_CHECK(_rhs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_report_message.svh", 269)
        ->__PVT___val;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base::__PVT___action 
        = VL_NULL_CHECK(rhs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_report_message.svh", 270)
        ->__PVT___action;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_do_clone(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base> &do_clone__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::__VnoInFunc_do_clone\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element> tmp;
    tmp = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element, vlSymsp);
    VL_NULL_CHECK(tmp, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_report_message.svh", 275)->__VnoInFunc_copy(vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element>{this});
    do_clone__Vfuncrtn = tmp;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element(uvmt_fifo_tb__Syms* __restrict vlSymsp)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base(vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_object_element::to_string_middle\n"); );
    // Body
    std::string out;
    out += "_val:" + VL_TO_STRING(__PVT___val);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_report_message_element_base::to_string_middle();
    return (out);
}
