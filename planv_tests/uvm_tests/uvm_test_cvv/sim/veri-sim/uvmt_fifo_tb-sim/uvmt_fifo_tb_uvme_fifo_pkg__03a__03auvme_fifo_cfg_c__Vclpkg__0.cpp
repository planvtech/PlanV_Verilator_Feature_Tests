// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi70> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi70> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi70__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvme_fifo_cfg_c"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi70> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi70__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c, vlProcess, vlSymsp, "uvme_fifo_cfg"s)
            : VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvme_fifo_cfg_c"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_do_execute_op(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op> op) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_do_execute_op\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::__VnoInFunc_do_execute_op(vlProcess, vlSymsp, op);
    this->__VnoInFunc____05Fm_uvm_execute_field_op(vlProcess, vlSymsp, op);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc____05Fm_uvm_execute_field_op(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op> ___05Flocal_op___05F) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc____05Fm_uvm_execute_field_op\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_get_rhs__5__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_get_rhs__6__Vfuncout;
    std::string __Vtask_get_name__7__Vfuncout;
    IData/*27:0*/ __Vtask_get_op_type__8__Vfuncout;
    __Vtask_get_op_type__8__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__9__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__10__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__11__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__12__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_policy> __Vtask_get_policy__13__Vfuncout;
    IData/*31:0*/ __Vtask_get_threshold__14__Vfuncout;
    __Vtask_get_threshold__14__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__15__Vfuncout;
    __Vtask_get_result__15__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__16__Vfuncout;
    __Vtask_get_threshold__16__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_field_int__17__Vfuncout;
    __Vtask_compare_field_int__17__Vfuncout = 0;
    CData/*0:0*/ __Vtask_is_open__20__Vfuncout;
    __Vtask_is_open__20__Vfuncout = 0;
    CData/*0:0*/ __Vtask_use_record_attribute__21__Vfuncout;
    __Vtask_use_record_attribute__21__Vfuncout = 0;
    QData/*63:0*/ __Vtask_read__25__Vfuncout;
    __Vtask_read__25__Vfuncout = 0;
    VlWide<128>/*4095:0*/ __Vtask_read__26__Vfuncout;
    VL_ZERO_W(4096, __Vtask_read__26__Vfuncout);
    IData/*31:0*/ __Vtask_read__27__Vfuncout;
    __Vtask_read__27__Vfuncout = 0;
    IData/*31:0*/ __Vtask_read__28__Vfuncout;
    __Vtask_read__28__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__29__Vfuncout;
    __Vtask_get_threshold__29__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__30__Vfuncout;
    __Vtask_get_result__30__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__31__Vfuncout;
    __Vtask_get_threshold__31__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_string__32__Vfuncout;
    __Vtask_compare_string__32__Vfuncout = 0;
    CData/*0:0*/ __Vtask_is_open__35__Vfuncout;
    __Vtask_is_open__35__Vfuncout = 0;
    CData/*0:0*/ __Vtask_use_record_attribute__36__Vfuncout;
    __Vtask_use_record_attribute__36__Vfuncout = 0;
    CData/*0:0*/ __Vtask_read__42__Vfuncout;
    __Vtask_read__42__Vfuncout = 0;
    std::string __Vtask_read__43__Vfuncout;
    CData/*0:0*/ __Vfunc_from_name__44__Vfuncout;
    __Vfunc_from_name__44__Vfuncout = 0;
    CData/*0:0*/ __Vtask_read__45__Vfuncout;
    __Vtask_read__45__Vfuncout = 0;
    QData/*63:0*/ __Vtask_read__46__Vfuncout;
    __Vtask_read__46__Vfuncout = 0;
    VlWide<128>/*4095:0*/ __Vtask_read__47__Vfuncout;
    VL_ZERO_W(4096, __Vtask_read__47__Vfuncout);
    IData/*31:0*/ __Vtask_read__48__Vfuncout;
    __Vtask_read__48__Vfuncout = 0;
    IData/*31:0*/ __Vtask_read__49__Vfuncout;
    __Vtask_read__49__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__50__Vfuncout;
    __Vtask_get_threshold__50__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__51__Vfuncout;
    __Vtask_get_result__51__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__52__Vfuncout;
    __Vtask_get_threshold__52__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_field_int__53__Vfuncout;
    __Vtask_compare_field_int__53__Vfuncout = 0;
    CData/*0:0*/ __Vtask_is_open__56__Vfuncout;
    __Vtask_is_open__56__Vfuncout = 0;
    CData/*0:0*/ __Vtask_use_record_attribute__57__Vfuncout;
    __Vtask_use_record_attribute__57__Vfuncout = 0;
    QData/*63:0*/ __Vtask_read__61__Vfuncout;
    __Vtask_read__61__Vfuncout = 0;
    VlWide<128>/*4095:0*/ __Vtask_read__62__Vfuncout;
    VL_ZERO_W(4096, __Vtask_read__62__Vfuncout);
    IData/*31:0*/ __Vtask_read__63__Vfuncout;
    __Vtask_read__63__Vfuncout = 0;
    IData/*31:0*/ __Vtask_read__64__Vfuncout;
    __Vtask_read__64__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__65__Vfuncout;
    __Vtask_get_threshold__65__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__66__Vfuncout;
    __Vtask_get_result__66__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__67__Vfuncout;
    __Vtask_get_threshold__67__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_field_int__68__Vfuncout;
    __Vtask_compare_field_int__68__Vfuncout = 0;
    CData/*0:0*/ __Vtask_is_open__71__Vfuncout;
    __Vtask_is_open__71__Vfuncout = 0;
    CData/*0:0*/ __Vtask_use_record_attribute__72__Vfuncout;
    __Vtask_use_record_attribute__72__Vfuncout = 0;
    QData/*63:0*/ __Vtask_read__76__Vfuncout;
    __Vtask_read__76__Vfuncout = 0;
    VlWide<128>/*4095:0*/ __Vtask_read__77__Vfuncout;
    VL_ZERO_W(4096, __Vtask_read__77__Vfuncout);
    IData/*31:0*/ __Vtask_read__78__Vfuncout;
    __Vtask_read__78__Vfuncout = 0;
    IData/*31:0*/ __Vtask_read__79__Vfuncout;
    __Vtask_read__79__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__80__Vfuncout;
    __Vtask_get_recursion_policy__80__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_first_copy__81__Vfuncout;
    __Vtask_get_first_copy__81__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__82__Vfuncout;
    __Vtask_get_recursion_policy__82__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__83__Vfuncout;
    __Vtask_get_recursion_policy__83__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_create__84__Vfuncout;
    std::string __Vtask_get_name__85__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__86__Vfuncout;
    __Vfunc_uvm_report_enabled__86__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__86__verbosity;
    __Vfunc_uvm_report_enabled__86__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__86__severity;
    __Vfunc_uvm_report_enabled__86__severity = 0;
    std::string __Vfunc_uvm_report_enabled__86__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__87__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__88__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__89__Vfuncout;
    __Vtask_uvm_report_enabled__89__Vfuncout = 0;
    std::string __Vtask_get_full_name__91__Vfuncout;
    std::string __Vtask_get_type_name__92__Vfuncout;
    IData/*31:0*/ __Vtask_object_copied__94__Vfuncout;
    __Vtask_object_copied__94__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__95__Vfuncout;
    __Vfunc_uvm_report_enabled__95__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__95__verbosity;
    __Vfunc_uvm_report_enabled__95__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__95__severity;
    __Vfunc_uvm_report_enabled__95__severity = 0;
    std::string __Vfunc_uvm_report_enabled__95__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__96__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__97__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__98__Vfuncout;
    __Vtask_uvm_report_enabled__98__Vfuncout = 0;
    std::string __Vtask_uvm_report_warning__99__id;
    std::string __Vtask_uvm_report_warning__99__message;
    IData/*31:0*/ __Vtask_uvm_report_warning__99__verbosity;
    __Vtask_uvm_report_warning__99__verbosity = 0;
    std::string __Vtask_uvm_report_warning__99__filename;
    IData/*31:0*/ __Vtask_uvm_report_warning__99__line;
    __Vtask_uvm_report_warning__99__line = 0;
    std::string __Vtask_uvm_report_warning__99__context_name;
    CData/*0:0*/ __Vtask_uvm_report_warning__99__report_enabled_checked;
    __Vtask_uvm_report_warning__99__report_enabled_checked = 0;
    std::string __Vtask_get_full_name__100__Vfuncout;
    std::string __Vtask_get_full_name__101__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__102__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__103__Vfuncout;
    IData/*31:0*/ __Vtask_get_threshold__106__Vfuncout;
    __Vtask_get_threshold__106__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__107__Vfuncout;
    __Vtask_get_result__107__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__108__Vfuncout;
    __Vtask_get_threshold__108__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__109__Vfuncout;
    __Vtask_get_recursion_policy__109__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__110__Vfuncout;
    __Vtask_get_recursion_policy__110__Vfuncout = 0;
    IData/*31:0*/ __Vtask_object_compared__111__Vfuncout;
    __Vtask_object_compared__111__Vfuncout = 0;
    CData/*0:0*/ __Vtask_object_compared__111__ret_val;
    __Vtask_object_compared__111__ret_val = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__112__Vfuncout;
    __Vtask_get_recursion_policy__112__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_object__114__Vfuncout;
    __Vtask_compare_object__114__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_object__115__Vfuncout;
    __Vtask_compare_object__115__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_unpack_object_with_meta__117__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__118__Vfuncout;
    __Vfunc_uvm_report_enabled__118__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__118__verbosity;
    __Vfunc_uvm_report_enabled__118__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__118__severity;
    __Vfunc_uvm_report_enabled__118__severity = 0;
    std::string __Vfunc_uvm_report_enabled__118__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__119__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__120__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__121__Vfuncout;
    __Vtask_uvm_report_enabled__121__Vfuncout = 0;
    std::string __Vtask_get_type_name__123__Vfuncout;
    IData/*31:0*/ __Vtask_object_printed__125__Vfuncout;
    __Vtask_object_printed__125__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__126__Vfuncout;
    __Vtask_get_recursion_policy__126__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__127__Vfuncout;
    __Vtask_get_recursion_policy__127__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_read__132__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__133__Vfuncout;
    __Vfunc_uvm_report_enabled__133__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__133__verbosity;
    __Vfunc_uvm_report_enabled__133__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__133__severity;
    __Vfunc_uvm_report_enabled__133__severity = 0;
    std::string __Vfunc_uvm_report_enabled__133__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__134__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__135__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__136__Vfuncout;
    __Vtask_uvm_report_enabled__136__Vfuncout = 0;
    std::string __Vtask_uvm_report_warning__137__id;
    std::string __Vtask_uvm_report_warning__137__message;
    IData/*31:0*/ __Vtask_uvm_report_warning__137__verbosity;
    __Vtask_uvm_report_warning__137__verbosity = 0;
    std::string __Vtask_uvm_report_warning__137__filename;
    IData/*31:0*/ __Vtask_uvm_report_warning__137__line;
    __Vtask_uvm_report_warning__137__line = 0;
    std::string __Vtask_uvm_report_warning__137__context_name;
    CData/*0:0*/ __Vtask_uvm_report_warning__137__report_enabled_checked;
    __Vtask_uvm_report_warning__137__report_enabled_checked = 0;
    std::string __Vfunc_get_full_name__138__Vfuncout;
    std::string __Vtask_get_type_name__139__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__140__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__141__Vfuncout;
    IData/*27:0*/ __Vtask_get_recursion_policy__143__Vfuncout;
    __Vtask_get_recursion_policy__143__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_first_copy__144__Vfuncout;
    __Vtask_get_first_copy__144__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__145__Vfuncout;
    __Vtask_get_recursion_policy__145__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__146__Vfuncout;
    __Vtask_get_recursion_policy__146__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_create__147__Vfuncout;
    std::string __Vtask_get_name__148__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__149__Vfuncout;
    __Vfunc_uvm_report_enabled__149__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__149__verbosity;
    __Vfunc_uvm_report_enabled__149__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__149__severity;
    __Vfunc_uvm_report_enabled__149__severity = 0;
    std::string __Vfunc_uvm_report_enabled__149__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__150__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__151__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__152__Vfuncout;
    __Vtask_uvm_report_enabled__152__Vfuncout = 0;
    std::string __Vtask_get_full_name__154__Vfuncout;
    std::string __Vtask_get_type_name__155__Vfuncout;
    IData/*31:0*/ __Vtask_object_copied__157__Vfuncout;
    __Vtask_object_copied__157__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__158__Vfuncout;
    __Vfunc_uvm_report_enabled__158__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__158__verbosity;
    __Vfunc_uvm_report_enabled__158__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__158__severity;
    __Vfunc_uvm_report_enabled__158__severity = 0;
    std::string __Vfunc_uvm_report_enabled__158__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__159__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__160__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__161__Vfuncout;
    __Vtask_uvm_report_enabled__161__Vfuncout = 0;
    std::string __Vtask_uvm_report_warning__162__id;
    std::string __Vtask_uvm_report_warning__162__message;
    IData/*31:0*/ __Vtask_uvm_report_warning__162__verbosity;
    __Vtask_uvm_report_warning__162__verbosity = 0;
    std::string __Vtask_uvm_report_warning__162__filename;
    IData/*31:0*/ __Vtask_uvm_report_warning__162__line;
    __Vtask_uvm_report_warning__162__line = 0;
    std::string __Vtask_uvm_report_warning__162__context_name;
    CData/*0:0*/ __Vtask_uvm_report_warning__162__report_enabled_checked;
    __Vtask_uvm_report_warning__162__report_enabled_checked = 0;
    std::string __Vtask_get_full_name__163__Vfuncout;
    std::string __Vtask_get_full_name__164__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__165__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__166__Vfuncout;
    IData/*31:0*/ __Vtask_get_threshold__169__Vfuncout;
    __Vtask_get_threshold__169__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__170__Vfuncout;
    __Vtask_get_result__170__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__171__Vfuncout;
    __Vtask_get_threshold__171__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__172__Vfuncout;
    __Vtask_get_recursion_policy__172__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__173__Vfuncout;
    __Vtask_get_recursion_policy__173__Vfuncout = 0;
    IData/*31:0*/ __Vtask_object_compared__174__Vfuncout;
    __Vtask_object_compared__174__Vfuncout = 0;
    CData/*0:0*/ __Vtask_object_compared__174__ret_val;
    __Vtask_object_compared__174__ret_val = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__175__Vfuncout;
    __Vtask_get_recursion_policy__175__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_object__177__Vfuncout;
    __Vtask_compare_object__177__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_object__178__Vfuncout;
    __Vtask_compare_object__178__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_unpack_object_with_meta__180__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__181__Vfuncout;
    __Vfunc_uvm_report_enabled__181__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__181__verbosity;
    __Vfunc_uvm_report_enabled__181__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__181__severity;
    __Vfunc_uvm_report_enabled__181__severity = 0;
    std::string __Vfunc_uvm_report_enabled__181__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__182__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__183__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__184__Vfuncout;
    __Vtask_uvm_report_enabled__184__Vfuncout = 0;
    std::string __Vtask_get_type_name__186__Vfuncout;
    IData/*31:0*/ __Vtask_object_printed__188__Vfuncout;
    __Vtask_object_printed__188__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__189__Vfuncout;
    __Vtask_get_recursion_policy__189__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__190__Vfuncout;
    __Vtask_get_recursion_policy__190__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_read__195__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__196__Vfuncout;
    __Vfunc_uvm_report_enabled__196__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__196__verbosity;
    __Vfunc_uvm_report_enabled__196__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__196__severity;
    __Vfunc_uvm_report_enabled__196__severity = 0;
    std::string __Vfunc_uvm_report_enabled__196__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__197__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__198__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__199__Vfuncout;
    __Vtask_uvm_report_enabled__199__Vfuncout = 0;
    std::string __Vtask_uvm_report_warning__200__id;
    std::string __Vtask_uvm_report_warning__200__message;
    IData/*31:0*/ __Vtask_uvm_report_warning__200__verbosity;
    __Vtask_uvm_report_warning__200__verbosity = 0;
    std::string __Vtask_uvm_report_warning__200__filename;
    IData/*31:0*/ __Vtask_uvm_report_warning__200__line;
    __Vtask_uvm_report_warning__200__line = 0;
    std::string __Vtask_uvm_report_warning__200__context_name;
    CData/*0:0*/ __Vtask_uvm_report_warning__200__report_enabled_checked;
    __Vtask_uvm_report_warning__200__report_enabled_checked = 0;
    std::string __Vfunc_get_full_name__201__Vfuncout;
    std::string __Vtask_get_type_name__202__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__203__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__204__Vfuncout;
    std::string __Vtemp_1;
    std::string __Vtemp_2;
    std::string __Vtemp_3;
    std::string __Vtemp_4;
    std::string __Vtemp_5;
    std::string __Vtemp_6;
    // Body
    VlQueue<CData/*0:0*/> unnamedblk1__DOT_____05Farray;
    unnamedblk1__DOT_____05Farray.atDefault() = 0;
    VlQueue<CData/*0:0*/> unnamedblk2__DOT_____05Farray;
    unnamedblk2__DOT_____05Farray.atDefault() = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz15> unnamedblk3__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz14> unnamedblk4__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_> unnamedblk5__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz16> unnamedblk6__DOT_____05Ftmp_rsrc___05F;
    VlQueue<CData/*0:0*/> unnamedblk7__DOT_____05Farray;
    unnamedblk7__DOT_____05Farray.atDefault() = 0;
    VlQueue<CData/*0:0*/> unnamedblk8__DOT_____05Farray;
    unnamedblk8__DOT_____05Farray.atDefault() = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz151> unnamedblk9__DOT_____05Ftmp_rsrc___05F;
    CData/*0:0*/ unnamedblk10__DOT_____05Ftmp_val___05F;
    unnamedblk10__DOT_____05Ftmp_val___05F = 0;
    std::string unnamedblk10__DOT_____05Ftmp_string_val___05F;
    CData/*0:0*/ unnamedblk10__DOT_____05Ftmp_success_val___05F;
    unnamedblk10__DOT_____05Ftmp_success_val___05F = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz5> unnamedblk10__DOT__unnamedblk11__DOT_____05Ftmp_rsrc___05F;
    CData/*0:0*/ unnamedblk12__DOT_____05Ftmp_int_val___05F;
    unnamedblk12__DOT_____05Ftmp_int_val___05F = 0;
    CData/*0:0*/ unnamedblk12__DOT_____05Ftmp_success_val___05F;
    unnamedblk12__DOT_____05Ftmp_success_val___05F = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz152> unnamedblk12__DOT__unnamedblk13__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz15> unnamedblk12__DOT__unnamedblk14__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz14> unnamedblk12__DOT__unnamedblk15__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_> unnamedblk12__DOT__unnamedblk16__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz16> unnamedblk12__DOT__unnamedblk17__DOT_____05Ftmp_rsrc___05F;
    VlQueue<CData/*0:0*/> unnamedblk18__DOT_____05Farray;
    unnamedblk18__DOT_____05Farray.atDefault() = 0;
    VlQueue<CData/*0:0*/> unnamedblk19__DOT_____05Farray;
    unnamedblk19__DOT_____05Farray.atDefault() = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz15> unnamedblk20__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz14> unnamedblk21__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_> unnamedblk22__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz16> unnamedblk23__DOT_____05Ftmp_rsrc___05F;
    VlQueue<CData/*0:0*/> unnamedblk24__DOT_____05Farray;
    unnamedblk24__DOT_____05Farray.atDefault() = 0;
    VlQueue<CData/*0:0*/> unnamedblk25__DOT_____05Farray;
    unnamedblk25__DOT_____05Farray.atDefault() = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz15> unnamedblk26__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz14> unnamedblk27__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_> unnamedblk28__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz16> unnamedblk29__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> unnamedblk30__DOT__lvalue_ref___05F;
    IData/*27:0*/ unnamedblk30__DOT__unnamedblk31__DOT__prev_pol___05F;
    unnamedblk30__DOT__unnamedblk31__DOT__prev_pol___05F = 0;
    IData/*27:0*/ unnamedblk30__DOT__unnamedblk31__DOT__curr_pol___05F;
    unnamedblk30__DOT__unnamedblk31__DOT__curr_pol___05F = 0;
    IData/*27:0*/ unnamedblk32__DOT__prev_rec___05F;
    unnamedblk32__DOT__prev_rec___05F = 0;
    CData/*0:0*/ unnamedblk32__DOT__unnamedblk33__DOT__rv;
    unnamedblk32__DOT__unnamedblk33__DOT__rv = 0;
    IData/*31:0*/ unnamedblk32__DOT__unnamedblk33__DOT__state;
    unnamedblk32__DOT__unnamedblk33__DOT__state = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> unnamedblk34__DOT_____05Fref;
    IData/*27:0*/ unnamedblk37__DOT_____05Fsaved_recursion_policy;
    unnamedblk37__DOT_____05Fsaved_recursion_policy = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz76> unnamedblk38__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> unnamedblk39__DOT__lvalue_ref___05F;
    IData/*27:0*/ unnamedblk39__DOT__unnamedblk40__DOT__prev_pol___05F;
    unnamedblk39__DOT__unnamedblk40__DOT__prev_pol___05F = 0;
    IData/*27:0*/ unnamedblk39__DOT__unnamedblk40__DOT__curr_pol___05F;
    unnamedblk39__DOT__unnamedblk40__DOT__curr_pol___05F = 0;
    IData/*27:0*/ unnamedblk41__DOT__prev_rec___05F;
    unnamedblk41__DOT__prev_rec___05F = 0;
    CData/*0:0*/ unnamedblk41__DOT__unnamedblk42__DOT__rv;
    unnamedblk41__DOT__unnamedblk42__DOT__rv = 0;
    IData/*31:0*/ unnamedblk41__DOT__unnamedblk42__DOT__state;
    unnamedblk41__DOT__unnamedblk42__DOT__state = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> unnamedblk43__DOT_____05Fref;
    IData/*27:0*/ unnamedblk46__DOT_____05Fsaved_recursion_policy;
    unnamedblk46__DOT_____05Fsaved_recursion_policy = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz76> unnamedblk47__DOT_____05Ftmp_rsrc___05F;
    IData/*27:0*/ local_op_type___05F;
    local_op_type___05F = 0;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c> local_rhs___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base> local_rsrc___05F;
    std::string local_rsrc_name___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> local_obj___05F;
    CData/*0:0*/ local_success___05F;
    local_success___05F = 0;
    IData/*31:0*/ local_size___05F;
    local_size___05F = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> ___05Flocal_printer___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_comparer> ___05Flocal_comparer___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> ___05Flocal_recorder___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_packer> ___05Flocal_packer___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_copier> ___05Flocal_copier___05F;
    {
        (void)VL_CAST_DYNAMIC(([&]() {
                    VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28)
                               ->__VnoInFunc_get_rhs(vlProcess, vlSymsp, __Vtask_get_rhs__5__Vfuncout);
                }(), __Vtask_get_rhs__5__Vfuncout), local_rhs___05F);
        if ((VL_CAST_DYNAMIC(([&]() {
                            VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28)
                              ->__VnoInFunc_get_rhs(vlProcess, vlSymsp, __Vtask_get_rhs__6__Vfuncout);
                        }(), __Vtask_get_rhs__6__Vfuncout), local_rsrc___05F) 
             && (VlNull{} != local_rsrc___05F))) {
            VL_NULL_CHECK(local_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28)->__VnoInFunc_get_name(vlSymsp, __Vtask_get_name__7__Vfuncout);
            local_rsrc_name___05F = __Vtask_get_name__7__Vfuncout;
        }
        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28)->__VnoInFunc_get_op_type(vlProcess, vlSymsp, __Vtask_get_op_type__8__Vfuncout);
        local_op_type___05F = __Vtask_get_op_type__8__Vfuncout;
        if ((0x00000010U == local_op_type___05F)) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__9__Vfuncout);
                                    }(), __Vtask_get_policy__9__Vfuncout), ___05Flocal_printer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cfg.svh:28: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cfg_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28, "");
            }
        } else if ((4U == local_op_type___05F)) {
            if ((VlNull{} == local_rhs___05F)) {
                goto __Vlabel0;
            }
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__10__Vfuncout);
                                    }(), __Vtask_get_policy__10__Vfuncout), ___05Flocal_comparer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cfg.svh:28: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cfg_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28, "");
            }
        } else if ((0x00000040U == local_op_type___05F)) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__11__Vfuncout);
                                    }(), __Vtask_get_policy__11__Vfuncout), ___05Flocal_recorder___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cfg.svh:28: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cfg_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28, "");
            }
        } else if (((0x00000100U == local_op_type___05F) 
                    || (0x00000400U == local_op_type___05F))) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__12__Vfuncout);
                                    }(), __Vtask_get_policy__12__Vfuncout), ___05Flocal_packer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cfg.svh:28: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cfg_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28, "");
            }
        } else if ((1U == local_op_type___05F)) {
            if ((VlNull{} == local_rhs___05F)) {
                goto __Vlabel0;
            }
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__13__Vfuncout);
                                    }(), __Vtask_get_policy__13__Vfuncout), ___05Flocal_copier___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cfg.svh:28: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cfg_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 28, "");
            }
        } else if ((0x00000800U == local_op_type___05F)) {
            if ((VlNull{} == local_rsrc___05F)) {
                goto __Vlabel0;
            }
        } else {
            goto __Vlabel0;
        }
        if ((1U == local_op_type___05F)) {
            this->__PVT__enabled = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                ->__PVT__enabled;
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__14__Vfuncout);
                                    }(), __Vtask_get_threshold__14__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__15__Vfuncout);
                            }(), __Vtask_get_result__15__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__16__Vfuncout);
                            }(), __Vtask_get_threshold__16__Vfuncout)))) {
                if (((IData)(this->__PVT__enabled) 
                     != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                     ->__PVT__enabled)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)->__VnoInFunc_compare_field_int(vlProcess, vlSymsp, "enabled"s, (QData)((IData)(this->__PVT__enabled)), (QData)((IData)(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                                                                                ->__PVT__enabled)), 1U, 0U, __Vtask_compare_field_int__17__Vfuncout);
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_UNPACK_RI_I(1, 1, unnamedblk1__DOT_____05Farray, VL_STREAML_FAST_III(1, (IData)(this->__PVT__enabled), 0));
            unnamedblk1__DOT_____05Farray.renew_copy(1U, unnamedblk1__DOT_____05Farray);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)->__VnoInFunc_pack_bits(vlProcess, vlSymsp, unnamedblk1__DOT_____05Farray, 1U);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk2__DOT_____05Farray.renew(1U);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)->__VnoInFunc_unpack_bits(vlProcess, vlSymsp, unnamedblk2__DOT_____05Farray, 1U);
            unnamedblk2__DOT_____05Farray.renew_copy(1U, unnamedblk2__DOT_____05Farray);
            this->__PVT__enabled = VL_STREAML_FAST_III(1, VL_PACK_I_RI
                                                       (1, 1, unnamedblk2__DOT_____05Farray), 0);
        } else if ((0x00000040U == local_op_type___05F)) {
            if (((VlNull{} != ___05Flocal_recorder___05F) 
                 && ([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                     ->__VnoInFunc_is_open(vlSymsp, __Vtask_is_open__20__Vfuncout);
                        }(), (IData)(__Vtask_is_open__20__Vfuncout)))) {
                if (([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                     ->__VnoInFunc_use_record_attribute(vlSymsp, __Vtask_use_record_attribute__21__Vfuncout);
                        }(), (IData)(__Vtask_use_record_attribute__21__Vfuncout))) {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)->__VnoInFunc_record_generic(vlProcess, vlSymsp, "enabled"s, VL_SFORMATF_N_NX("%0#",0,
                                                                                1,
                                                                                this->__PVT__enabled) , ""s);
                } else {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)->__VnoInFunc_record_field_int(vlProcess, vlSymsp, "enabled"s, (QData)((IData)(this->__PVT__enabled)), 1U, 0U);
                }
            }
        } else if ((0x00000010U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)->__VnoInFunc_print_field_int(vlProcess, vlSymsp, "enabled"s, (QData)((IData)(this->__PVT__enabled)), 1U, 0U, 0x2eU, "integral"s);
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("enabled"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk3__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    this->__PVT__enabled = (1U & (IData)(
                                                         ([&]() {
                                    VL_NULL_CHECK(unnamedblk3__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                                                          ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                             VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__25__Vfuncout);
                                }(), __Vtask_read__25__Vfuncout)));
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk4__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__enabled = (1U 
                                                & VL_BITSEL_IWII(4096, 
                                                                 ([&]() {
                                        VL_NULL_CHECK(unnamedblk4__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                                                                  ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__26__Vfuncout);
                                    }(), __Vtask_read__26__Vfuncout), 0U));
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk5__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__enabled = (1U 
                                                & ([&]() {
                                    VL_NULL_CHECK(unnamedblk5__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                                                   ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                      VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__27__Vfuncout);
                                }(), __Vtask_read__27__Vfuncout));
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk6__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__enabled = (1U 
                                                & ([&]() {
                                    VL_NULL_CHECK(unnamedblk6__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 29)
                                                   ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                      VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__28__Vfuncout);
                                }(), __Vtask_read__28__Vfuncout));
                    }
                }
            }
        }
        if ((1U == local_op_type___05F)) {
            this->__PVT__is_active = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                ->__PVT__is_active;
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__29__Vfuncout);
                                    }(), __Vtask_get_threshold__29__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__30__Vfuncout);
                            }(), __Vtask_get_result__30__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__31__Vfuncout);
                            }(), __Vtask_get_threshold__31__Vfuncout)))) {
                if (((IData)(this->__PVT__is_active) 
                     != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                     ->__PVT__is_active)) {
                    __Vtemp_1 = uvmt_fifo_tb___024unit::__Venumtab_enum_name19
                        [this->__PVT__is_active];
                    __Vtemp_2 = uvmt_fifo_tb___024unit::__Venumtab_enum_name19
                        [VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                        ->__PVT__is_active];
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_compare_string(vlProcess, vlSymsp, "is_active"s, VL_SFORMATF_N_NX("uvm_active_passive_enum'(%@)",0,
                                                                                -1,
                                                                                &(__Vtemp_1)) , VL_SFORMATF_N_NX("uvm_active_passive_enum'(%@)",0,
                                                                                -1,
                                                                                &(__Vtemp_2)) , __Vtask_compare_string__32__Vfuncout);
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_UNPACK_RI_I(1, 1, unnamedblk7__DOT_____05Farray, VL_STREAML_FAST_III(1, (IData)(this->__PVT__is_active), 0));
            unnamedblk7__DOT_____05Farray.renew_copy(1U, unnamedblk7__DOT_____05Farray);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_pack_bits(vlProcess, vlSymsp, unnamedblk7__DOT_____05Farray, 1U);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk8__DOT_____05Farray.renew(1U);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_unpack_bits(vlProcess, vlSymsp, unnamedblk8__DOT_____05Farray, 1U);
            unnamedblk8__DOT_____05Farray.renew_copy(1U, unnamedblk8__DOT_____05Farray);
            this->__PVT__is_active = VL_STREAML_FAST_III(1, VL_PACK_I_RI
                                                         (1, 1, unnamedblk8__DOT_____05Farray), 0);
        } else if ((0x00000040U == local_op_type___05F)) {
            if (((VlNull{} != ___05Flocal_recorder___05F) 
                 && ([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                     ->__VnoInFunc_is_open(vlSymsp, __Vtask_is_open__35__Vfuncout);
                        }(), (IData)(__Vtask_is_open__35__Vfuncout)))) {
                if (([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                     ->__VnoInFunc_use_record_attribute(vlSymsp, __Vtask_use_record_attribute__36__Vfuncout);
                        }(), (IData)(__Vtask_use_record_attribute__36__Vfuncout))) {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_record_generic(vlProcess, vlSymsp, "is_active"s, VL_SFORMATF_N_NX("%0#",0,
                                                                                1,
                                                                                this->__PVT__is_active) , ""s);
                } else if ((""s == uvmt_fifo_tb___024unit::__Venumtab_enum_name19
                            [this->__PVT__is_active])) {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_record_generic(vlProcess, vlSymsp, "is_active"s, VL_SFORMATF_N_NX("%0#",0,
                                                                                1,
                                                                                this->__PVT__is_active) , "uvm_active_passive_enum"s);
                } else {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_record_generic(vlProcess, vlSymsp, "is_active"s, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                uvmt_fifo_tb___024unit::__Venumtab_enum_name19
                                                                                [this->__PVT__is_active]), "uvm_active_passive_enum"s);
                }
            }
        } else if ((0x00000010U == local_op_type___05F)) {
            if ((""s == uvmt_fifo_tb___024unit::__Venumtab_enum_name19
                 [this->__PVT__is_active])) {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_print_field_int(vlProcess, vlSymsp, "is_active"s, (QData)((IData)(this->__PVT__is_active)), 1U, 0U, 0x2eU, "uvm_active_passive_enum"s);
            } else {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_print_generic(vlProcess, vlSymsp, "is_active"s, "uvm_active_passive_enum"s, 1U, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                uvmt_fifo_tb___024unit::__Venumtab_enum_name19
                                                                                [this->__PVT__is_active]), 0x2eU);
            }
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("is_active"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk9__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    VL_NULL_CHECK(unnamedblk9__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__42__Vfuncout);
                    this->__PVT__is_active = __Vtask_read__42__Vfuncout;
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    unnamedblk10__DOT_____05Ftmp_success_val___05F 
                        = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk10__DOT__unnamedblk11__DOT_____05Ftmp_rsrc___05F));
                    if (unnamedblk10__DOT_____05Ftmp_success_val___05F) {
                        VL_NULL_CHECK(unnamedblk10__DOT__unnamedblk11__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__43__Vfuncout);
                        unnamedblk10__DOT_____05Ftmp_string_val___05F 
                            = __Vtask_read__43__Vfuncout;
                    }
                    if (((IData)(unnamedblk10__DOT_____05Ftmp_success_val___05F) 
                         && ([&]() {
                                    vlSymsp->TOP__uvm_pkg__03a__03auvm_enum_wrapper___Vclpkg.__VnoInFunc_from_name(vlSymsp, unnamedblk10__DOT_____05Ftmp_string_val___05F, unnamedblk10__DOT_____05Ftmp_val___05F, __Vfunc_from_name__44__Vfuncout);
                                }(), (IData)(__Vfunc_from_name__44__Vfuncout)))) {
                        this->__PVT__is_active = unnamedblk10__DOT_____05Ftmp_val___05F;
                        local_success___05F = unnamedblk10__DOT_____05Ftmp_success_val___05F;
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    unnamedblk12__DOT_____05Ftmp_success_val___05F 
                        = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk12__DOT__unnamedblk13__DOT_____05Ftmp_rsrc___05F));
                    if (unnamedblk12__DOT_____05Ftmp_success_val___05F) {
                        VL_NULL_CHECK(unnamedblk12__DOT__unnamedblk13__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__45__Vfuncout);
                        unnamedblk12__DOT_____05Ftmp_int_val___05F 
                            = __Vtask_read__45__Vfuncout;
                    }
                    if ((1U & (~ (IData)(unnamedblk12__DOT_____05Ftmp_success_val___05F)))) {
                        unnamedblk12__DOT_____05Ftmp_success_val___05F 
                            = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk12__DOT__unnamedblk14__DOT_____05Ftmp_rsrc___05F));
                        if (unnamedblk12__DOT_____05Ftmp_success_val___05F) {
                            unnamedblk12__DOT_____05Ftmp_int_val___05F 
                                = (1U & (IData)(([&]() {
                                            VL_NULL_CHECK(unnamedblk12__DOT__unnamedblk14__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                                                 ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__46__Vfuncout);
                                        }(), __Vtask_read__46__Vfuncout)));
                        }
                        if ((1U & (~ (IData)(unnamedblk12__DOT_____05Ftmp_success_val___05F)))) {
                            unnamedblk12__DOT_____05Ftmp_success_val___05F 
                                = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk12__DOT__unnamedblk15__DOT_____05Ftmp_rsrc___05F));
                            if (unnamedblk12__DOT_____05Ftmp_success_val___05F) {
                                unnamedblk12__DOT_____05Ftmp_int_val___05F 
                                    = (1U & VL_BITSEL_IWII(4096, 
                                                           ([&]() {
                                                VL_NULL_CHECK(unnamedblk12__DOT__unnamedblk15__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                                                            ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                               VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__47__Vfuncout);
                                            }(), __Vtask_read__47__Vfuncout), 0U));
                            }
                        }
                        if ((1U & (~ (IData)(unnamedblk12__DOT_____05Ftmp_success_val___05F)))) {
                            unnamedblk12__DOT_____05Ftmp_success_val___05F 
                                = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk12__DOT__unnamedblk16__DOT_____05Ftmp_rsrc___05F));
                            if (unnamedblk12__DOT_____05Ftmp_success_val___05F) {
                                unnamedblk12__DOT_____05Ftmp_int_val___05F 
                                    = (1U & ([&]() {
                                            VL_NULL_CHECK(unnamedblk12__DOT__unnamedblk16__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                                             ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__48__Vfuncout);
                                        }(), __Vtask_read__48__Vfuncout));
                            }
                        }
                        if ((1U & (~ (IData)(unnamedblk12__DOT_____05Ftmp_success_val___05F)))) {
                            unnamedblk12__DOT_____05Ftmp_success_val___05F 
                                = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk12__DOT__unnamedblk17__DOT_____05Ftmp_rsrc___05F));
                            if (unnamedblk12__DOT_____05Ftmp_success_val___05F) {
                                unnamedblk12__DOT_____05Ftmp_int_val___05F 
                                    = (1U & ([&]() {
                                            VL_NULL_CHECK(unnamedblk12__DOT__unnamedblk17__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 30)
                                             ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__49__Vfuncout);
                                        }(), __Vtask_read__49__Vfuncout));
                            }
                        }
                    }
                    if (unnamedblk12__DOT_____05Ftmp_success_val___05F) {
                        this->__PVT__is_active = unnamedblk12__DOT_____05Ftmp_int_val___05F;
                        local_success___05F = unnamedblk12__DOT_____05Ftmp_success_val___05F;
                    }
                }
            }
        }
        if ((1U == local_op_type___05F)) {
            this->__PVT__scoreboard_enabled = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                ->__PVT__scoreboard_enabled;
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__50__Vfuncout);
                                    }(), __Vtask_get_threshold__50__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__51__Vfuncout);
                            }(), __Vtask_get_result__51__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__52__Vfuncout);
                            }(), __Vtask_get_threshold__52__Vfuncout)))) {
                if (((IData)(this->__PVT__scoreboard_enabled) 
                     != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                     ->__PVT__scoreboard_enabled)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)->__VnoInFunc_compare_field_int(vlProcess, vlSymsp, "scoreboard_enabled"s, (QData)((IData)(this->__PVT__scoreboard_enabled)), (QData)((IData)(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                                                                                ->__PVT__scoreboard_enabled)), 1U, 0U, __Vtask_compare_field_int__53__Vfuncout);
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_UNPACK_RI_I(1, 1, unnamedblk18__DOT_____05Farray, VL_STREAML_FAST_III(1, (IData)(this->__PVT__scoreboard_enabled), 0));
            unnamedblk18__DOT_____05Farray.renew_copy(1U, unnamedblk18__DOT_____05Farray);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)->__VnoInFunc_pack_bits(vlProcess, vlSymsp, unnamedblk18__DOT_____05Farray, 1U);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk19__DOT_____05Farray.renew(1U);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)->__VnoInFunc_unpack_bits(vlProcess, vlSymsp, unnamedblk19__DOT_____05Farray, 1U);
            unnamedblk19__DOT_____05Farray.renew_copy(1U, unnamedblk19__DOT_____05Farray);
            this->__PVT__scoreboard_enabled = VL_STREAML_FAST_III(1, VL_PACK_I_RI
                                                                  (1, 1, unnamedblk19__DOT_____05Farray), 0);
        } else if ((0x00000040U == local_op_type___05F)) {
            if (((VlNull{} != ___05Flocal_recorder___05F) 
                 && ([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                     ->__VnoInFunc_is_open(vlSymsp, __Vtask_is_open__56__Vfuncout);
                        }(), (IData)(__Vtask_is_open__56__Vfuncout)))) {
                if (([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                     ->__VnoInFunc_use_record_attribute(vlSymsp, __Vtask_use_record_attribute__57__Vfuncout);
                        }(), (IData)(__Vtask_use_record_attribute__57__Vfuncout))) {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)->__VnoInFunc_record_generic(vlProcess, vlSymsp, "scoreboard_enabled"s, VL_SFORMATF_N_NX("%0#",0,
                                                                                1,
                                                                                this->__PVT__scoreboard_enabled) , ""s);
                } else {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)->__VnoInFunc_record_field_int(vlProcess, vlSymsp, "scoreboard_enabled"s, (QData)((IData)(this->__PVT__scoreboard_enabled)), 1U, 0U);
                }
            }
        } else if ((0x00000010U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)->__VnoInFunc_print_field_int(vlProcess, vlSymsp, "scoreboard_enabled"s, (QData)((IData)(this->__PVT__scoreboard_enabled)), 1U, 0U, 0x2eU, "integral"s);
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("scoreboard_enabled"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk20__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    this->__PVT__scoreboard_enabled 
                        = (1U & (IData)(([&]() {
                                    VL_NULL_CHECK(unnamedblk20__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                                         ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                            VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__61__Vfuncout);
                                }(), __Vtask_read__61__Vfuncout)));
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk21__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__scoreboard_enabled 
                            = (1U & VL_BITSEL_IWII(4096, 
                                                   ([&]() {
                                        VL_NULL_CHECK(unnamedblk21__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                                                    ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                       VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__62__Vfuncout);
                                    }(), __Vtask_read__62__Vfuncout), 0U));
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk22__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__scoreboard_enabled 
                            = (1U & ([&]() {
                                    VL_NULL_CHECK(unnamedblk22__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                                     ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                        VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__63__Vfuncout);
                                }(), __Vtask_read__63__Vfuncout));
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk23__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__scoreboard_enabled 
                            = (1U & ([&]() {
                                    VL_NULL_CHECK(unnamedblk23__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 31)
                                     ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                        VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__64__Vfuncout);
                                }(), __Vtask_read__64__Vfuncout));
                    }
                }
            }
        }
        if ((1U == local_op_type___05F)) {
            this->__PVT__cov_model_enabled = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                ->__PVT__cov_model_enabled;
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__65__Vfuncout);
                                    }(), __Vtask_get_threshold__65__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__66__Vfuncout);
                            }(), __Vtask_get_result__66__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__67__Vfuncout);
                            }(), __Vtask_get_threshold__67__Vfuncout)))) {
                if (((IData)(this->__PVT__cov_model_enabled) 
                     != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                     ->__PVT__cov_model_enabled)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)->__VnoInFunc_compare_field_int(vlProcess, vlSymsp, "cov_model_enabled"s, (QData)((IData)(this->__PVT__cov_model_enabled)), (QData)((IData)(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                                                                                ->__PVT__cov_model_enabled)), 1U, 0U, __Vtask_compare_field_int__68__Vfuncout);
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_UNPACK_RI_I(1, 1, unnamedblk24__DOT_____05Farray, VL_STREAML_FAST_III(1, (IData)(this->__PVT__cov_model_enabled), 0));
            unnamedblk24__DOT_____05Farray.renew_copy(1U, unnamedblk24__DOT_____05Farray);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)->__VnoInFunc_pack_bits(vlProcess, vlSymsp, unnamedblk24__DOT_____05Farray, 1U);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk25__DOT_____05Farray.renew(1U);
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)->__VnoInFunc_unpack_bits(vlProcess, vlSymsp, unnamedblk25__DOT_____05Farray, 1U);
            unnamedblk25__DOT_____05Farray.renew_copy(1U, unnamedblk25__DOT_____05Farray);
            this->__PVT__cov_model_enabled = VL_STREAML_FAST_III(1, VL_PACK_I_RI
                                                                 (1, 1, unnamedblk25__DOT_____05Farray), 0);
        } else if ((0x00000040U == local_op_type___05F)) {
            if (((VlNull{} != ___05Flocal_recorder___05F) 
                 && ([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                     ->__VnoInFunc_is_open(vlSymsp, __Vtask_is_open__71__Vfuncout);
                        }(), (IData)(__Vtask_is_open__71__Vfuncout)))) {
                if (([&]() {
                            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                     ->__VnoInFunc_use_record_attribute(vlSymsp, __Vtask_use_record_attribute__72__Vfuncout);
                        }(), (IData)(__Vtask_use_record_attribute__72__Vfuncout))) {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)->__VnoInFunc_record_generic(vlProcess, vlSymsp, "cov_model_enabled"s, VL_SFORMATF_N_NX("%0#",0,
                                                                                1,
                                                                                this->__PVT__cov_model_enabled) , ""s);
                } else {
                    VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)->__VnoInFunc_record_field_int(vlProcess, vlSymsp, "cov_model_enabled"s, (QData)((IData)(this->__PVT__cov_model_enabled)), 1U, 0U);
                }
            }
        } else if ((0x00000010U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)->__VnoInFunc_print_field_int(vlProcess, vlSymsp, "cov_model_enabled"s, (QData)((IData)(this->__PVT__cov_model_enabled)), 1U, 0U, 0x2eU, "integral"s);
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("cov_model_enabled"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk26__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    this->__PVT__cov_model_enabled 
                        = (1U & (IData)(([&]() {
                                    VL_NULL_CHECK(unnamedblk26__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                                         ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                            VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__76__Vfuncout);
                                }(), __Vtask_read__76__Vfuncout)));
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk27__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__cov_model_enabled 
                            = (1U & VL_BITSEL_IWII(4096, 
                                                   ([&]() {
                                        VL_NULL_CHECK(unnamedblk27__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                                                    ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                       VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__77__Vfuncout);
                                    }(), __Vtask_read__77__Vfuncout), 0U));
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk28__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__cov_model_enabled 
                            = (1U & ([&]() {
                                    VL_NULL_CHECK(unnamedblk28__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                                     ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                        VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__78__Vfuncout);
                                }(), __Vtask_read__78__Vfuncout));
                    }
                }
                if ((1U & (~ (IData)(local_success___05F)))) {
                    local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk29__DOT_____05Ftmp_rsrc___05F));
                    if (local_success___05F) {
                        this->__PVT__cov_model_enabled 
                            = (1U & ([&]() {
                                    VL_NULL_CHECK(unnamedblk29__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 32)
                                     ->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                        VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__79__Vfuncout);
                                }(), __Vtask_read__79__Vfuncout));
                    }
                }
            }
        }
        if ((1U == local_op_type___05F)) {
            if ((this->__PVT__read_cfg != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                 ->__PVT__read_cfg)) {
                if (((VlNull{} == VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                      ->__PVT__read_cfg) || (0x00040000U 
                                             == ([&]() {
                                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                 ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__80__Vfuncout);
                                }(), __Vtask_get_recursion_policy__80__Vfuncout)))) {
                    this->__PVT__read_cfg = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                        ->__PVT__read_cfg;
                } else if (((1U & (~ (0U != ([&]() {
                                            VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                             ->__VnoInFunc_get_first_copy(vlSymsp, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                          ->__PVT__read_cfg, unnamedblk30__DOT__lvalue_ref___05F, __Vtask_get_first_copy__81__Vfuncout);
                                        }(), __Vtask_get_first_copy__81__Vfuncout)))) 
                            || (! VL_CAST_DYNAMIC(unnamedblk30__DOT__lvalue_ref___05F, this->__PVT__read_cfg)))) {
                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__82__Vfuncout);
                    unnamedblk30__DOT__unnamedblk31__DOT__prev_pol___05F 
                        = __Vtask_get_recursion_policy__82__Vfuncout;
                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__83__Vfuncout);
                    unnamedblk30__DOT__unnamedblk31__DOT__curr_pol___05F 
                        = __Vtask_get_recursion_policy__83__Vfuncout;
                    if ((VlNull{} == this->__PVT__read_cfg)) {
                        if (((0U == VL_CAST_DYNAMIC(
                                                    ([&]() {
                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                              ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                     ->__VnoInFunc_create(vlProcess, vlSymsp, 
                                                                          VL_CVT_PACK_STR_NN(
                                                                                ([&]() {
                                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                              ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__VnoInFunc_get_name(vlSymsp, __Vtask_get_name__85__Vfuncout);
                                                            }(), __Vtask_get_name__85__Vfuncout)), __Vtask_create__84__Vfuncout);
                                            }(), __Vtask_create__84__Vfuncout), this->__PVT__read_cfg)) 
                             || (VlNull{} == this->__PVT__read_cfg))) {
                            if ((0U != ([&]() {
                                            __Vfunc_uvm_report_enabled__86__id = "UVM/COPY/NULL_CREATE"s;
                                            __Vfunc_uvm_report_enabled__86__severity = 3U;
                                            __Vfunc_uvm_report_enabled__86__verbosity = 0U;
                                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__87__Vfuncout);
                                            vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                                = __Vfunc_get__87__Vfuncout;
                                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                        ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__88__Vfuncout);
                                            vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                                = __Vtask_get_root__88__Vfuncout;
                                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                        ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__86__verbosity, (IData)(__Vfunc_uvm_report_enabled__86__severity), __Vfunc_uvm_report_enabled__86__id, __Vtask_uvm_report_enabled__89__Vfuncout);
                                            __Vfunc_uvm_report_enabled__86__Vfuncout 
                                                = __Vtask_uvm_report_enabled__89__Vfuncout;
                                        }(), __Vfunc_uvm_report_enabled__86__Vfuncout))) {
                                vlSymsp->TOP__uvm_pkg.__VnoInFunc_uvm_report_fatal_TOP__uvm_pkg(vlProcess, vlSymsp, "UVM/COPY/NULL_CREATE"s, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Could not create '"s, 
                                                                                ([&]() {
                                                                        VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__91__Vfuncout);
                                                                    }(), __Vtask_get_full_name__91__Vfuncout)), "' of type '"s), 
                                                                                ([&]() {
                                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                              ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__92__Vfuncout);
                                                            }(), __Vtask_get_type_name__92__Vfuncout)), "', into '"s), "read_cfg"s), "'."s)), 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh"s, 0x00000021U, ""s, 1U);
                            }
                        } else {
                            VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_copy_object(vlProcess, vlSymsp, this->__PVT__read_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__PVT__read_cfg);
                        }
                    } else if ((1U == ([&]() {
                                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                       ->__VnoInFunc_object_copied(vlSymsp, this->__PVT__read_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                   ->__PVT__read_cfg, unnamedblk30__DOT__unnamedblk31__DOT__curr_pol___05F, __Vtask_object_copied__94__Vfuncout);
                                }(), __Vtask_object_copied__94__Vfuncout))) {
                        if ((0U != ([&]() {
                                        __Vfunc_uvm_report_enabled__95__id = "UVM/COPY/LOOP"s;
                                        __Vfunc_uvm_report_enabled__95__severity = 1U;
                                        __Vfunc_uvm_report_enabled__95__verbosity = 0U;
                                        vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__96__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                            = __Vfunc_get__96__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                    ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__97__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                            = __Vtask_get_root__97__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                    ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__95__verbosity, (IData)(__Vfunc_uvm_report_enabled__95__severity), __Vfunc_uvm_report_enabled__95__id, __Vtask_uvm_report_enabled__98__Vfuncout);
                                        __Vfunc_uvm_report_enabled__95__Vfuncout 
                                            = __Vtask_uvm_report_enabled__98__Vfuncout;
                                    }(), __Vfunc_uvm_report_enabled__95__Vfuncout))) {
                            __Vtask_uvm_report_warning__99__report_enabled_checked = 1U;
                            __Vtask_uvm_report_warning__99__context_name = ""s;
                            __Vtask_uvm_report_warning__99__line = 0x00000021U;
                            __Vtask_uvm_report_warning__99__filename = "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh"s;
                            __Vtask_uvm_report_warning__99__verbosity = 0U;
                            __Vtask_uvm_report_warning__99__message 
                                = VL_CVT_PACK_STR_NN(
                                                     VL_CONCATN_NNN(
                                                                    VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Loop detected in copy operation (LHS:'"s, 
                                                                                ([&]() {
                                                        VL_NULL_CHECK(this->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__100__Vfuncout);
                                                    }(), __Vtask_get_full_name__100__Vfuncout)), "', RHS:'"s), 
                                                                                ([&]() {
                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                              ->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__101__Vfuncout);
                                            }(), __Vtask_get_full_name__101__Vfuncout)), "')"s));
                            __Vtask_uvm_report_warning__99__id = "UVM/COPY/LOOP"s;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__102__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs 
                                = __Vfunc_get__102__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 155)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__103__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top 
                                = __Vtask_get_root__103__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 156)->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, __Vtask_uvm_report_warning__99__id, __Vtask_uvm_report_warning__99__message, __Vtask_uvm_report_warning__99__verbosity, __Vtask_uvm_report_warning__99__filename, __Vtask_uvm_report_warning__99__line, __Vtask_uvm_report_warning__99__context_name, (IData)(__Vtask_uvm_report_warning__99__report_enabled_checked));
                        }
                    } else {
                        VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_copy_object(vlProcess, vlSymsp, this->__PVT__read_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__PVT__read_cfg);
                    }
                }
            }
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__106__Vfuncout);
                                    }(), __Vtask_get_threshold__106__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__107__Vfuncout);
                            }(), __Vtask_get_result__107__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__108__Vfuncout);
                            }(), __Vtask_get_threshold__108__Vfuncout)))) {
                if ((this->__PVT__read_cfg != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                     ->__PVT__read_cfg)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__109__Vfuncout);
                    unnamedblk32__DOT__prev_rec___05F 
                        = __Vtask_get_recursion_policy__109__Vfuncout;
                    if ((0x00040000U != ([&]() {
                                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                         ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__110__Vfuncout);
                                }(), __Vtask_get_recursion_policy__110__Vfuncout))) {
                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_object_compared(vlSymsp, this->__PVT__read_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__PVT__read_cfg, 
                                                                                ([&]() {
                                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__112__Vfuncout);
                                }(), __Vtask_get_recursion_policy__112__Vfuncout), __Vtask_object_compared__111__ret_val, __Vtask_object_compared__111__Vfuncout);
                        unnamedblk32__DOT__unnamedblk33__DOT__rv 
                            = __Vtask_object_compared__111__ret_val;
                        unnamedblk32__DOT__unnamedblk33__DOT__state 
                            = __Vtask_object_compared__111__Vfuncout;
                        if (((2U == unnamedblk32__DOT__unnamedblk33__DOT__state) 
                             & (~ (IData)(unnamedblk32__DOT__unnamedblk33__DOT__rv)))) {
                            VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_print_msg(vlProcess, vlSymsp, "'read_cfg' miscompared using saved return value"s);
                        } else if ((0U == unnamedblk32__DOT__unnamedblk33__DOT__state)) {
                            VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_compare_object(vlProcess, vlSymsp, "read_cfg"s, this->__PVT__read_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__PVT__read_cfg, __Vtask_compare_object__114__Vfuncout);
                        }
                    } else {
                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_compare_object(vlProcess, vlSymsp, "read_cfg"s, this->__PVT__read_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__PVT__read_cfg, __Vtask_compare_object__115__Vfuncout);
                    }
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_pack_object_with_meta(vlProcess, vlSymsp, this->__PVT__read_cfg);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk34__DOT_____05Fref = this->__PVT__read_cfg;
            __Vtask_unpack_object_with_meta__117__value 
                = unnamedblk34__DOT_____05Fref;
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_unpack_object_with_meta(vlProcess, vlSymsp, __Vtask_unpack_object_with_meta__117__value);
            unnamedblk34__DOT_____05Fref = __Vtask_unpack_object_with_meta__117__value;
            if (((unnamedblk34__DOT_____05Fref != this->__PVT__read_cfg) 
                 && (! VL_CAST_DYNAMIC(unnamedblk34__DOT_____05Fref, this->__PVT__read_cfg)))) {
                if ((0U != ([&]() {
                                __Vfunc_uvm_report_enabled__118__id = "UVM/UNPACK_EXT/OBJ_CAST_FAILED"s;
                                __Vfunc_uvm_report_enabled__118__severity = 3U;
                                __Vfunc_uvm_report_enabled__118__verbosity = 0U;
                                vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__119__Vfuncout);
                                vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                    = __Vfunc_get__119__Vfuncout;
                                VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                            ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__120__Vfuncout);
                                vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                    = __Vtask_get_root__120__Vfuncout;
                                VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                            ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__118__verbosity, (IData)(__Vfunc_uvm_report_enabled__118__severity), __Vfunc_uvm_report_enabled__118__id, __Vtask_uvm_report_enabled__121__Vfuncout);
                                __Vfunc_uvm_report_enabled__118__Vfuncout 
                                    = __Vtask_uvm_report_enabled__121__Vfuncout;
                            }(), __Vfunc_uvm_report_enabled__118__Vfuncout))) {
                    vlSymsp->TOP__uvm_pkg.__VnoInFunc_uvm_report_fatal_TOP__uvm_pkg(vlProcess, vlSymsp, "UVM/UNPACK_EXT/OBJ_CAST_FAILED"s, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Could not cast object of type '"s, 
                                                                                ([&]() {
                                                VL_NULL_CHECK(unnamedblk34__DOT_____05Fref, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                                                ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__123__Vfuncout);
                                            }(), __Vtask_get_type_name__123__Vfuncout)), "' into '"s), "LVALUE"s)), 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh"s, 0x00000021U, ""s, 1U);
                }
            }
        } else if ((0x00000040U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_record_object(vlProcess, vlSymsp, "read_cfg"s, this->__PVT__read_cfg);
        } else if ((0x00000010U == local_op_type___05F)) {
            if ((0U != ([&]() {
                            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                        ->__VnoInFunc_object_printed(vlSymsp, this->__PVT__read_cfg, 
                                                     ([&]() {
                                        VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                                      ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__126__Vfuncout);
                                    }(), __Vtask_get_recursion_policy__126__Vfuncout), __Vtask_object_printed__125__Vfuncout);
                        }(), __Vtask_object_printed__125__Vfuncout))) {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__127__Vfuncout);
                unnamedblk37__DOT_____05Fsaved_recursion_policy 
                    = __Vtask_get_recursion_policy__127__Vfuncout;
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_set_recursion_policy(vlSymsp, 0x00040000U);
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_print_object(vlProcess, vlSymsp, "read_cfg"s, this->__PVT__read_cfg, 0x2eU);
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_set_recursion_policy(vlSymsp, unnamedblk37__DOT_____05Fsaved_recursion_policy);
            } else {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_print_object(vlProcess, vlSymsp, "read_cfg"s, this->__PVT__read_cfg, 0x2eU);
            }
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("read_cfg"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk38__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    VL_NULL_CHECK(unnamedblk38__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__132__Vfuncout);
                    local_obj___05F = __Vtask_read__132__Vfuncout;
                }
                if (local_success___05F) {
                    if ((VlNull{} == local_obj___05F)) {
                        this->__PVT__read_cfg = VlNull{};
                    } else if ((! VL_CAST_DYNAMIC(local_obj___05F, this->__PVT__read_cfg))) {
                        if ((0U != ([&]() {
                                        __Vfunc_uvm_report_enabled__133__id = "UVM/FIELDS/OBJ_TYPE"s;
                                        __Vfunc_uvm_report_enabled__133__severity = 1U;
                                        __Vfunc_uvm_report_enabled__133__verbosity = 0U;
                                        vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__134__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                            = __Vfunc_get__134__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                    ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__135__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                            = __Vtask_get_root__135__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                    ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__133__verbosity, (IData)(__Vfunc_uvm_report_enabled__133__severity), __Vfunc_uvm_report_enabled__133__id, __Vtask_uvm_report_enabled__136__Vfuncout);
                                        __Vfunc_uvm_report_enabled__133__Vfuncout 
                                            = __Vtask_uvm_report_enabled__136__Vfuncout;
                                    }(), __Vfunc_uvm_report_enabled__133__Vfuncout))) {
                            __Vtask_uvm_report_warning__137__report_enabled_checked = 1U;
                            __Vtask_uvm_report_warning__137__context_name = ""s;
                            __Vtask_uvm_report_warning__137__line = 0x00000021U;
                            __Vtask_uvm_report_warning__137__filename = "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh"s;
                            __Vtask_uvm_report_warning__137__verbosity = 0U;
                            __Vtemp_3 = ([&]() {
                                    this->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vfunc_get_full_name__138__Vfuncout);
                                }(), __Vfunc_get_full_name__138__Vfuncout);
                            __Vtemp_4 = ([&]() {
                                    VL_NULL_CHECK(local_obj___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 33)
                                         ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__139__Vfuncout);
                                }(), __Vtask_get_type_name__139__Vfuncout);
                            __Vtask_uvm_report_warning__137__message 
                                = VL_SFORMATF_N_NX("Can't set field 'read_cfg' on '%@' with '%@' type",0,
                                                   -1,
                                                   &(__Vtemp_3),
                                                   -1,
                                                   &(__Vtemp_4)) ;
                            __Vtask_uvm_report_warning__137__id = "UVM/FIELDS/OBJ_TYPE"s;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__140__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs 
                                = __Vfunc_get__140__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 155)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__141__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top 
                                = __Vtask_get_root__141__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 156)->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, __Vtask_uvm_report_warning__137__id, __Vtask_uvm_report_warning__137__message, __Vtask_uvm_report_warning__137__verbosity, __Vtask_uvm_report_warning__137__filename, __Vtask_uvm_report_warning__137__line, __Vtask_uvm_report_warning__137__context_name, (IData)(__Vtask_uvm_report_warning__137__report_enabled_checked));
                        }
                    }
                }
            }
        }
        if ((1U == local_op_type___05F)) {
            if ((this->__PVT__write_cfg != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                 ->__PVT__write_cfg)) {
                if (((VlNull{} == VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                      ->__PVT__write_cfg) || (0x00040000U 
                                              == ([&]() {
                                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                  ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__143__Vfuncout);
                                }(), __Vtask_get_recursion_policy__143__Vfuncout)))) {
                    this->__PVT__write_cfg = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                        ->__PVT__write_cfg;
                } else if (((1U & (~ (0U != ([&]() {
                                            VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                             ->__VnoInFunc_get_first_copy(vlSymsp, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                          ->__PVT__write_cfg, unnamedblk39__DOT__lvalue_ref___05F, __Vtask_get_first_copy__144__Vfuncout);
                                        }(), __Vtask_get_first_copy__144__Vfuncout)))) 
                            || (! VL_CAST_DYNAMIC(unnamedblk39__DOT__lvalue_ref___05F, this->__PVT__write_cfg)))) {
                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__145__Vfuncout);
                    unnamedblk39__DOT__unnamedblk40__DOT__prev_pol___05F 
                        = __Vtask_get_recursion_policy__145__Vfuncout;
                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__146__Vfuncout);
                    unnamedblk39__DOT__unnamedblk40__DOT__curr_pol___05F 
                        = __Vtask_get_recursion_policy__146__Vfuncout;
                    if ((VlNull{} == this->__PVT__write_cfg)) {
                        if (((0U == VL_CAST_DYNAMIC(
                                                    ([&]() {
                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                              ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                     ->__VnoInFunc_create(vlProcess, vlSymsp, 
                                                                          VL_CVT_PACK_STR_NN(
                                                                                ([&]() {
                                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                              ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__VnoInFunc_get_name(vlSymsp, __Vtask_get_name__148__Vfuncout);
                                                            }(), __Vtask_get_name__148__Vfuncout)), __Vtask_create__147__Vfuncout);
                                            }(), __Vtask_create__147__Vfuncout), this->__PVT__write_cfg)) 
                             || (VlNull{} == this->__PVT__write_cfg))) {
                            if ((0U != ([&]() {
                                            __Vfunc_uvm_report_enabled__149__id = "UVM/COPY/NULL_CREATE"s;
                                            __Vfunc_uvm_report_enabled__149__severity = 3U;
                                            __Vfunc_uvm_report_enabled__149__verbosity = 0U;
                                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__150__Vfuncout);
                                            vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                                = __Vfunc_get__150__Vfuncout;
                                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                        ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__151__Vfuncout);
                                            vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                                = __Vtask_get_root__151__Vfuncout;
                                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                        ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__149__verbosity, (IData)(__Vfunc_uvm_report_enabled__149__severity), __Vfunc_uvm_report_enabled__149__id, __Vtask_uvm_report_enabled__152__Vfuncout);
                                            __Vfunc_uvm_report_enabled__149__Vfuncout 
                                                = __Vtask_uvm_report_enabled__152__Vfuncout;
                                        }(), __Vfunc_uvm_report_enabled__149__Vfuncout))) {
                                vlSymsp->TOP__uvm_pkg.__VnoInFunc_uvm_report_fatal_TOP__uvm_pkg(vlProcess, vlSymsp, "UVM/COPY/NULL_CREATE"s, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Could not create '"s, 
                                                                                ([&]() {
                                                                        VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__154__Vfuncout);
                                                                    }(), __Vtask_get_full_name__154__Vfuncout)), "' of type '"s), 
                                                                                ([&]() {
                                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                              ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__155__Vfuncout);
                                                            }(), __Vtask_get_type_name__155__Vfuncout)), "', into '"s), "write_cfg"s), "'."s)), 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh"s, 0x00000022U, ""s, 1U);
                            }
                        } else {
                            VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_copy_object(vlProcess, vlSymsp, this->__PVT__write_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__PVT__write_cfg);
                        }
                    } else if ((1U == ([&]() {
                                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                       ->__VnoInFunc_object_copied(vlSymsp, this->__PVT__write_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                   ->__PVT__write_cfg, unnamedblk39__DOT__unnamedblk40__DOT__curr_pol___05F, __Vtask_object_copied__157__Vfuncout);
                                }(), __Vtask_object_copied__157__Vfuncout))) {
                        if ((0U != ([&]() {
                                        __Vfunc_uvm_report_enabled__158__id = "UVM/COPY/LOOP"s;
                                        __Vfunc_uvm_report_enabled__158__severity = 1U;
                                        __Vfunc_uvm_report_enabled__158__verbosity = 0U;
                                        vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__159__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                            = __Vfunc_get__159__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                    ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__160__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                            = __Vtask_get_root__160__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                    ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__158__verbosity, (IData)(__Vfunc_uvm_report_enabled__158__severity), __Vfunc_uvm_report_enabled__158__id, __Vtask_uvm_report_enabled__161__Vfuncout);
                                        __Vfunc_uvm_report_enabled__158__Vfuncout 
                                            = __Vtask_uvm_report_enabled__161__Vfuncout;
                                    }(), __Vfunc_uvm_report_enabled__158__Vfuncout))) {
                            __Vtask_uvm_report_warning__162__report_enabled_checked = 1U;
                            __Vtask_uvm_report_warning__162__context_name = ""s;
                            __Vtask_uvm_report_warning__162__line = 0x00000022U;
                            __Vtask_uvm_report_warning__162__filename = "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh"s;
                            __Vtask_uvm_report_warning__162__verbosity = 0U;
                            __Vtask_uvm_report_warning__162__message 
                                = VL_CVT_PACK_STR_NN(
                                                     VL_CONCATN_NNN(
                                                                    VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Loop detected in copy operation (LHS:'"s, 
                                                                                ([&]() {
                                                        VL_NULL_CHECK(this->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__163__Vfuncout);
                                                    }(), __Vtask_get_full_name__163__Vfuncout)), "', RHS:'"s), 
                                                                                ([&]() {
                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                              ->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__164__Vfuncout);
                                            }(), __Vtask_get_full_name__164__Vfuncout)), "')"s));
                            __Vtask_uvm_report_warning__162__id = "UVM/COPY/LOOP"s;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__165__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs 
                                = __Vfunc_get__165__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 155)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__166__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top 
                                = __Vtask_get_root__166__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 156)->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, __Vtask_uvm_report_warning__162__id, __Vtask_uvm_report_warning__162__message, __Vtask_uvm_report_warning__162__verbosity, __Vtask_uvm_report_warning__162__filename, __Vtask_uvm_report_warning__162__line, __Vtask_uvm_report_warning__162__context_name, (IData)(__Vtask_uvm_report_warning__162__report_enabled_checked));
                        }
                    } else {
                        VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_copy_object(vlProcess, vlSymsp, this->__PVT__write_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__PVT__write_cfg);
                    }
                }
            }
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__169__Vfuncout);
                                    }(), __Vtask_get_threshold__169__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__170__Vfuncout);
                            }(), __Vtask_get_result__170__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__171__Vfuncout);
                            }(), __Vtask_get_threshold__171__Vfuncout)))) {
                if ((this->__PVT__write_cfg != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                     ->__PVT__write_cfg)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__172__Vfuncout);
                    unnamedblk41__DOT__prev_rec___05F 
                        = __Vtask_get_recursion_policy__172__Vfuncout;
                    if ((0x00040000U != ([&]() {
                                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                         ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__173__Vfuncout);
                                }(), __Vtask_get_recursion_policy__173__Vfuncout))) {
                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_object_compared(vlSymsp, this->__PVT__write_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__PVT__write_cfg, 
                                                                                ([&]() {
                                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__175__Vfuncout);
                                }(), __Vtask_get_recursion_policy__175__Vfuncout), __Vtask_object_compared__174__ret_val, __Vtask_object_compared__174__Vfuncout);
                        unnamedblk41__DOT__unnamedblk42__DOT__rv 
                            = __Vtask_object_compared__174__ret_val;
                        unnamedblk41__DOT__unnamedblk42__DOT__state 
                            = __Vtask_object_compared__174__Vfuncout;
                        if (((2U == unnamedblk41__DOT__unnamedblk42__DOT__state) 
                             & (~ (IData)(unnamedblk41__DOT__unnamedblk42__DOT__rv)))) {
                            VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_print_msg(vlProcess, vlSymsp, "'write_cfg' miscompared using saved return value"s);
                        } else if ((0U == unnamedblk41__DOT__unnamedblk42__DOT__state)) {
                            VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_compare_object(vlProcess, vlSymsp, "write_cfg"s, this->__PVT__write_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__PVT__write_cfg, __Vtask_compare_object__177__Vfuncout);
                        }
                    } else {
                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_compare_object(vlProcess, vlSymsp, "write_cfg"s, this->__PVT__write_cfg, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__PVT__write_cfg, __Vtask_compare_object__178__Vfuncout);
                    }
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_pack_object_with_meta(vlProcess, vlSymsp, this->__PVT__write_cfg);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk43__DOT_____05Fref = this->__PVT__write_cfg;
            __Vtask_unpack_object_with_meta__180__value 
                = unnamedblk43__DOT_____05Fref;
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_unpack_object_with_meta(vlProcess, vlSymsp, __Vtask_unpack_object_with_meta__180__value);
            unnamedblk43__DOT_____05Fref = __Vtask_unpack_object_with_meta__180__value;
            if (((unnamedblk43__DOT_____05Fref != this->__PVT__write_cfg) 
                 && (! VL_CAST_DYNAMIC(unnamedblk43__DOT_____05Fref, this->__PVT__write_cfg)))) {
                if ((0U != ([&]() {
                                __Vfunc_uvm_report_enabled__181__id = "UVM/UNPACK_EXT/OBJ_CAST_FAILED"s;
                                __Vfunc_uvm_report_enabled__181__severity = 3U;
                                __Vfunc_uvm_report_enabled__181__verbosity = 0U;
                                vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__182__Vfuncout);
                                vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                    = __Vfunc_get__182__Vfuncout;
                                VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                            ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__183__Vfuncout);
                                vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                    = __Vtask_get_root__183__Vfuncout;
                                VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                            ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__181__verbosity, (IData)(__Vfunc_uvm_report_enabled__181__severity), __Vfunc_uvm_report_enabled__181__id, __Vtask_uvm_report_enabled__184__Vfuncout);
                                __Vfunc_uvm_report_enabled__181__Vfuncout 
                                    = __Vtask_uvm_report_enabled__184__Vfuncout;
                            }(), __Vfunc_uvm_report_enabled__181__Vfuncout))) {
                    vlSymsp->TOP__uvm_pkg.__VnoInFunc_uvm_report_fatal_TOP__uvm_pkg(vlProcess, vlSymsp, "UVM/UNPACK_EXT/OBJ_CAST_FAILED"s, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Could not cast object of type '"s, 
                                                                                ([&]() {
                                                VL_NULL_CHECK(unnamedblk43__DOT_____05Fref, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                                                ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__186__Vfuncout);
                                            }(), __Vtask_get_type_name__186__Vfuncout)), "' into '"s), "LVALUE"s)), 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh"s, 0x00000022U, ""s, 1U);
                }
            }
        } else if ((0x00000040U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_record_object(vlProcess, vlSymsp, "write_cfg"s, this->__PVT__write_cfg);
        } else if ((0x00000010U == local_op_type___05F)) {
            if ((0U != ([&]() {
                            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                        ->__VnoInFunc_object_printed(vlSymsp, this->__PVT__write_cfg, 
                                                     ([&]() {
                                        VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                                      ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__189__Vfuncout);
                                    }(), __Vtask_get_recursion_policy__189__Vfuncout), __Vtask_object_printed__188__Vfuncout);
                        }(), __Vtask_object_printed__188__Vfuncout))) {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__190__Vfuncout);
                unnamedblk46__DOT_____05Fsaved_recursion_policy 
                    = __Vtask_get_recursion_policy__190__Vfuncout;
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_set_recursion_policy(vlSymsp, 0x00040000U);
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_print_object(vlProcess, vlSymsp, "write_cfg"s, this->__PVT__write_cfg, 0x2eU);
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_set_recursion_policy(vlSymsp, unnamedblk46__DOT_____05Fsaved_recursion_policy);
            } else {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_print_object(vlProcess, vlSymsp, "write_cfg"s, this->__PVT__write_cfg, 0x2eU);
            }
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("write_cfg"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk47__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    VL_NULL_CHECK(unnamedblk47__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>{this}, __Vtask_read__195__Vfuncout);
                    local_obj___05F = __Vtask_read__195__Vfuncout;
                }
                if (local_success___05F) {
                    if ((VlNull{} == local_obj___05F)) {
                        this->__PVT__write_cfg = VlNull{};
                    } else if ((! VL_CAST_DYNAMIC(local_obj___05F, this->__PVT__write_cfg))) {
                        if ((0U != ([&]() {
                                        __Vfunc_uvm_report_enabled__196__id = "UVM/FIELDS/OBJ_TYPE"s;
                                        __Vfunc_uvm_report_enabled__196__severity = 1U;
                                        __Vfunc_uvm_report_enabled__196__verbosity = 0U;
                                        vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__197__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                            = __Vfunc_get__197__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                    ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__198__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                            = __Vtask_get_root__198__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                    ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__196__verbosity, (IData)(__Vfunc_uvm_report_enabled__196__severity), __Vfunc_uvm_report_enabled__196__id, __Vtask_uvm_report_enabled__199__Vfuncout);
                                        __Vfunc_uvm_report_enabled__196__Vfuncout 
                                            = __Vtask_uvm_report_enabled__199__Vfuncout;
                                    }(), __Vfunc_uvm_report_enabled__196__Vfuncout))) {
                            __Vtask_uvm_report_warning__200__report_enabled_checked = 1U;
                            __Vtask_uvm_report_warning__200__context_name = ""s;
                            __Vtask_uvm_report_warning__200__line = 0x00000022U;
                            __Vtask_uvm_report_warning__200__filename = "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh"s;
                            __Vtask_uvm_report_warning__200__verbosity = 0U;
                            __Vtemp_5 = ([&]() {
                                    this->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vfunc_get_full_name__201__Vfuncout);
                                }(), __Vfunc_get_full_name__201__Vfuncout);
                            __Vtemp_6 = ([&]() {
                                    VL_NULL_CHECK(local_obj___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 34)
                                         ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__202__Vfuncout);
                                }(), __Vtask_get_type_name__202__Vfuncout);
                            __Vtask_uvm_report_warning__200__message 
                                = VL_SFORMATF_N_NX("Can't set field 'write_cfg' on '%@' with '%@' type",0,
                                                   -1,
                                                   &(__Vtemp_5),
                                                   -1,
                                                   &(__Vtemp_6)) ;
                            __Vtask_uvm_report_warning__200__id = "UVM/FIELDS/OBJ_TYPE"s;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__203__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs 
                                = __Vfunc_get__203__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 155)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__204__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top 
                                = __Vtask_get_root__204__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 156)->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, __Vtask_uvm_report_warning__200__id, __Vtask_uvm_report_warning__200__message, __Vtask_uvm_report_warning__200__verbosity, __Vtask_uvm_report_warning__200__filename, __Vtask_uvm_report_warning__200__line, __Vtask_uvm_report_warning__200__context_name, (IData)(__Vtask_uvm_report_warning__200__report_enabled_checked));
                        }
                    }
                }
            }
        }
        __Vlabel0: ;
    }
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_object(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::new\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cfg_c> __Vfunc_create__207__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cfg_c> __Vfunc_create__208__Vfuncout;
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi84__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "write_cfg"s, VlNull{}, ""s, __Vfunc_create__207__Vfuncout);
    this->__PVT__write_cfg = __Vfunc_create__207__Vfuncout;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi84__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "read_cfg"s, VlNull{}, ""s, __Vfunc_create__208__Vfuncout);
    this->__PVT__read_cfg = __Vfunc_create__208__Vfuncout;
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(this->__PVT__enabled, 1ULL, 
                                                                        "enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(this->__PVT__is_active, 1ULL, 
                                                                        "is_active", 0ULL);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__211__Vfuncout;
    __Vfunc___VBasicRand__211__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 48)
                                                                        ->__PVT__enabled, 1ULL, 
                                                                        "write_cfg.enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 49)
                                                                        ->__PVT__enabled, 1ULL, 
                                                                        "read_cfg.enabled", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 53)
                                                                        ->__PVT__is_active, 1ULL, 
                                                                        "write_cfg.is_active", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 54)
                                                                        ->__PVT__is_active, 1ULL, 
                                                                        "read_cfg.is_active", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__write_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 57)
                                                                        ->__PVT__wr_or_rd, 1ULL, 
                                                                        "write_cfg.wr_or_rd", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.write_var(VL_NULL_CHECK(this->__PVT__read_cfg, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cfg.svh", 58)
                                                                        ->__PVT__wr_or_rd, 1ULL, 
                                                                        "read_cfg.wr_or_rd", 0ULL);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__211__Vfuncout);
            }(), __Vfunc___VBasicRand__211__Vfuncout));
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_agent_cfg_cons_setup_constraint(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc_agent_cfg_cons_setup_constraint\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (=> (__Vbool enabled) (__Vbool (bvand (__Vbv (= ((_ zero_extend 31) write_cfg.enabled) #x00000001)) (__Vbv (= ((_ zero_extend 31) read_cfg.enabled) #x00000001))))))"s);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (=> (__Vbool (__Vbv (= is_active #b1))) (__Vbool (bvand (__Vbv (= write_cfg.is_active #b1)) (__Vbv (= read_cfg.is_active #b1))))))"s);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (= write_cfg.wr_or_rd #b0))"s);
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.hard("(__Vbv (= read_cfg.wr_or_rd #b1))"s);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::__VnoInFunc___Vsetup_constraints\n"); );
    // Body
    this->__VnoInFunc_agent_cfg_cons_setup_constraint(vlSymsp);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__enabled = 0;
    __PVT__is_active = 0;
    __PVT__scoreboard_enabled = 0;
    __PVT__cov_model_enabled = 0;
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+            uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cfg_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += "enabled:" + VL_TO_STRING(__PVT__enabled);
    out += ", is_active:" + VL_TO_STRING(__PVT__is_active);
    out += ", scoreboard_enabled:" + VL_TO_STRING(__PVT__scoreboard_enabled);
    out += ", cov_model_enabled:" + VL_TO_STRING(__PVT__cov_model_enabled);
    out += ", write_cfg:" + VL_TO_STRING(__PVT__write_cfg);
    out += ", read_cfg:" + VL_TO_STRING(__PVT__read_cfg);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::to_string_middle();
    return (out);
}
