// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi71> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi71> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi71__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvme_fifo_cntxt_c"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__pi71> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi71__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c, vlProcess, vlSymsp, "uvme_fifo_cntxt"s)
            : VL_NEW(uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvme_fifo_cntxt_c"s;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_do_execute_op(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op> op) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_do_execute_op\n"); );
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::__VnoInFunc_do_execute_op(vlProcess, vlSymsp, op);
    this->__VnoInFunc____05Fm_uvm_execute_field_op(vlProcess, vlSymsp, op);
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc____05Fm_uvm_execute_field_op(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_field_op> ___05Flocal_op___05F) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc____05Fm_uvm_execute_field_op\n"); );
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
    IData/*27:0*/ __Vtask_get_recursion_policy__14__Vfuncout;
    __Vtask_get_recursion_policy__14__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_first_copy__15__Vfuncout;
    __Vtask_get_first_copy__15__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__16__Vfuncout;
    __Vtask_get_recursion_policy__16__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__17__Vfuncout;
    __Vtask_get_recursion_policy__17__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_create__18__Vfuncout;
    std::string __Vtask_get_name__19__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__20__Vfuncout;
    __Vfunc_uvm_report_enabled__20__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__20__verbosity;
    __Vfunc_uvm_report_enabled__20__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__20__severity;
    __Vfunc_uvm_report_enabled__20__severity = 0;
    std::string __Vfunc_uvm_report_enabled__20__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__21__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__22__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__23__Vfuncout;
    __Vtask_uvm_report_enabled__23__Vfuncout = 0;
    std::string __Vtask_get_full_name__25__Vfuncout;
    std::string __Vtask_get_type_name__26__Vfuncout;
    IData/*31:0*/ __Vtask_object_copied__28__Vfuncout;
    __Vtask_object_copied__28__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__29__Vfuncout;
    __Vfunc_uvm_report_enabled__29__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__29__verbosity;
    __Vfunc_uvm_report_enabled__29__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__29__severity;
    __Vfunc_uvm_report_enabled__29__severity = 0;
    std::string __Vfunc_uvm_report_enabled__29__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__30__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__31__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__32__Vfuncout;
    __Vtask_uvm_report_enabled__32__Vfuncout = 0;
    std::string __Vtask_uvm_report_warning__33__id;
    std::string __Vtask_uvm_report_warning__33__message;
    IData/*31:0*/ __Vtask_uvm_report_warning__33__verbosity;
    __Vtask_uvm_report_warning__33__verbosity = 0;
    std::string __Vtask_uvm_report_warning__33__filename;
    IData/*31:0*/ __Vtask_uvm_report_warning__33__line;
    __Vtask_uvm_report_warning__33__line = 0;
    std::string __Vtask_uvm_report_warning__33__context_name;
    CData/*0:0*/ __Vtask_uvm_report_warning__33__report_enabled_checked;
    __Vtask_uvm_report_warning__33__report_enabled_checked = 0;
    std::string __Vtask_get_full_name__34__Vfuncout;
    std::string __Vtask_get_full_name__35__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__36__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__37__Vfuncout;
    IData/*31:0*/ __Vtask_get_threshold__40__Vfuncout;
    __Vtask_get_threshold__40__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__41__Vfuncout;
    __Vtask_get_result__41__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__42__Vfuncout;
    __Vtask_get_threshold__42__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__43__Vfuncout;
    __Vtask_get_recursion_policy__43__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__44__Vfuncout;
    __Vtask_get_recursion_policy__44__Vfuncout = 0;
    IData/*31:0*/ __Vtask_object_compared__45__Vfuncout;
    __Vtask_object_compared__45__Vfuncout = 0;
    CData/*0:0*/ __Vtask_object_compared__45__ret_val;
    __Vtask_object_compared__45__ret_val = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__46__Vfuncout;
    __Vtask_get_recursion_policy__46__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_object__48__Vfuncout;
    __Vtask_compare_object__48__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_object__49__Vfuncout;
    __Vtask_compare_object__49__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_unpack_object_with_meta__51__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__52__Vfuncout;
    __Vfunc_uvm_report_enabled__52__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__52__verbosity;
    __Vfunc_uvm_report_enabled__52__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__52__severity;
    __Vfunc_uvm_report_enabled__52__severity = 0;
    std::string __Vfunc_uvm_report_enabled__52__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__53__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__54__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__55__Vfuncout;
    __Vtask_uvm_report_enabled__55__Vfuncout = 0;
    std::string __Vtask_get_type_name__57__Vfuncout;
    IData/*31:0*/ __Vtask_object_printed__59__Vfuncout;
    __Vtask_object_printed__59__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__60__Vfuncout;
    __Vtask_get_recursion_policy__60__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__61__Vfuncout;
    __Vtask_get_recursion_policy__61__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_read__66__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__67__Vfuncout;
    __Vfunc_uvm_report_enabled__67__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__67__verbosity;
    __Vfunc_uvm_report_enabled__67__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__67__severity;
    __Vfunc_uvm_report_enabled__67__severity = 0;
    std::string __Vfunc_uvm_report_enabled__67__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__68__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__69__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__70__Vfuncout;
    __Vtask_uvm_report_enabled__70__Vfuncout = 0;
    std::string __Vtask_uvm_report_warning__71__id;
    std::string __Vtask_uvm_report_warning__71__message;
    IData/*31:0*/ __Vtask_uvm_report_warning__71__verbosity;
    __Vtask_uvm_report_warning__71__verbosity = 0;
    std::string __Vtask_uvm_report_warning__71__filename;
    IData/*31:0*/ __Vtask_uvm_report_warning__71__line;
    __Vtask_uvm_report_warning__71__line = 0;
    std::string __Vtask_uvm_report_warning__71__context_name;
    CData/*0:0*/ __Vtask_uvm_report_warning__71__report_enabled_checked;
    __Vtask_uvm_report_warning__71__report_enabled_checked = 0;
    std::string __Vfunc_get_full_name__72__Vfuncout;
    std::string __Vtask_get_type_name__73__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__74__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__75__Vfuncout;
    IData/*27:0*/ __Vtask_get_recursion_policy__77__Vfuncout;
    __Vtask_get_recursion_policy__77__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_first_copy__78__Vfuncout;
    __Vtask_get_first_copy__78__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__79__Vfuncout;
    __Vtask_get_recursion_policy__79__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__80__Vfuncout;
    __Vtask_get_recursion_policy__80__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_create__81__Vfuncout;
    std::string __Vtask_get_name__82__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__83__Vfuncout;
    __Vfunc_uvm_report_enabled__83__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__83__verbosity;
    __Vfunc_uvm_report_enabled__83__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__83__severity;
    __Vfunc_uvm_report_enabled__83__severity = 0;
    std::string __Vfunc_uvm_report_enabled__83__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__84__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__85__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__86__Vfuncout;
    __Vtask_uvm_report_enabled__86__Vfuncout = 0;
    std::string __Vtask_get_full_name__88__Vfuncout;
    std::string __Vtask_get_type_name__89__Vfuncout;
    IData/*31:0*/ __Vtask_object_copied__91__Vfuncout;
    __Vtask_object_copied__91__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__92__Vfuncout;
    __Vfunc_uvm_report_enabled__92__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__92__verbosity;
    __Vfunc_uvm_report_enabled__92__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__92__severity;
    __Vfunc_uvm_report_enabled__92__severity = 0;
    std::string __Vfunc_uvm_report_enabled__92__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__93__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__94__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__95__Vfuncout;
    __Vtask_uvm_report_enabled__95__Vfuncout = 0;
    std::string __Vtask_uvm_report_warning__96__id;
    std::string __Vtask_uvm_report_warning__96__message;
    IData/*31:0*/ __Vtask_uvm_report_warning__96__verbosity;
    __Vtask_uvm_report_warning__96__verbosity = 0;
    std::string __Vtask_uvm_report_warning__96__filename;
    IData/*31:0*/ __Vtask_uvm_report_warning__96__line;
    __Vtask_uvm_report_warning__96__line = 0;
    std::string __Vtask_uvm_report_warning__96__context_name;
    CData/*0:0*/ __Vtask_uvm_report_warning__96__report_enabled_checked;
    __Vtask_uvm_report_warning__96__report_enabled_checked = 0;
    std::string __Vtask_get_full_name__97__Vfuncout;
    std::string __Vtask_get_full_name__98__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__99__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__100__Vfuncout;
    IData/*31:0*/ __Vtask_get_threshold__103__Vfuncout;
    __Vtask_get_threshold__103__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_result__104__Vfuncout;
    __Vtask_get_result__104__Vfuncout = 0;
    IData/*31:0*/ __Vtask_get_threshold__105__Vfuncout;
    __Vtask_get_threshold__105__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__106__Vfuncout;
    __Vtask_get_recursion_policy__106__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__107__Vfuncout;
    __Vtask_get_recursion_policy__107__Vfuncout = 0;
    IData/*31:0*/ __Vtask_object_compared__108__Vfuncout;
    __Vtask_object_compared__108__Vfuncout = 0;
    CData/*0:0*/ __Vtask_object_compared__108__ret_val;
    __Vtask_object_compared__108__ret_val = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__109__Vfuncout;
    __Vtask_get_recursion_policy__109__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_object__111__Vfuncout;
    __Vtask_compare_object__111__Vfuncout = 0;
    CData/*0:0*/ __Vtask_compare_object__112__Vfuncout;
    __Vtask_compare_object__112__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_unpack_object_with_meta__114__value;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__115__Vfuncout;
    __Vfunc_uvm_report_enabled__115__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__115__verbosity;
    __Vfunc_uvm_report_enabled__115__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__115__severity;
    __Vfunc_uvm_report_enabled__115__severity = 0;
    std::string __Vfunc_uvm_report_enabled__115__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__116__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__117__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__118__Vfuncout;
    __Vtask_uvm_report_enabled__118__Vfuncout = 0;
    std::string __Vtask_get_type_name__120__Vfuncout;
    IData/*31:0*/ __Vtask_object_printed__122__Vfuncout;
    __Vtask_object_printed__122__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__123__Vfuncout;
    __Vtask_get_recursion_policy__123__Vfuncout = 0;
    IData/*27:0*/ __Vtask_get_recursion_policy__124__Vfuncout;
    __Vtask_get_recursion_policy__124__Vfuncout = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> __Vtask_read__129__Vfuncout;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__130__Vfuncout;
    __Vfunc_uvm_report_enabled__130__Vfuncout = 0;
    IData/*31:0*/ __Vfunc_uvm_report_enabled__130__verbosity;
    __Vfunc_uvm_report_enabled__130__verbosity = 0;
    CData/*1:0*/ __Vfunc_uvm_report_enabled__130__severity;
    __Vfunc_uvm_report_enabled__130__severity = 0;
    std::string __Vfunc_uvm_report_enabled__130__id;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__131__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__132__Vfuncout;
    IData/*31:0*/ __Vtask_uvm_report_enabled__133__Vfuncout;
    __Vtask_uvm_report_enabled__133__Vfuncout = 0;
    std::string __Vtask_uvm_report_warning__134__id;
    std::string __Vtask_uvm_report_warning__134__message;
    IData/*31:0*/ __Vtask_uvm_report_warning__134__verbosity;
    __Vtask_uvm_report_warning__134__verbosity = 0;
    std::string __Vtask_uvm_report_warning__134__filename;
    IData/*31:0*/ __Vtask_uvm_report_warning__134__line;
    __Vtask_uvm_report_warning__134__line = 0;
    std::string __Vtask_uvm_report_warning__134__context_name;
    CData/*0:0*/ __Vtask_uvm_report_warning__134__report_enabled_checked;
    __Vtask_uvm_report_warning__134__report_enabled_checked = 0;
    std::string __Vfunc_get_full_name__135__Vfuncout;
    std::string __Vtask_get_type_name__136__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__137__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__138__Vfuncout;
    std::string __Vtemp_1;
    std::string __Vtemp_2;
    std::string __Vtemp_3;
    std::string __Vtemp_4;
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> unnamedblk1__DOT__lvalue_ref___05F;
    IData/*27:0*/ unnamedblk1__DOT__unnamedblk2__DOT__prev_pol___05F;
    unnamedblk1__DOT__unnamedblk2__DOT__prev_pol___05F = 0;
    IData/*27:0*/ unnamedblk1__DOT__unnamedblk2__DOT__curr_pol___05F;
    unnamedblk1__DOT__unnamedblk2__DOT__curr_pol___05F = 0;
    IData/*27:0*/ unnamedblk3__DOT__prev_rec___05F;
    unnamedblk3__DOT__prev_rec___05F = 0;
    CData/*0:0*/ unnamedblk3__DOT__unnamedblk4__DOT__rv;
    unnamedblk3__DOT__unnamedblk4__DOT__rv = 0;
    IData/*31:0*/ unnamedblk3__DOT__unnamedblk4__DOT__state;
    unnamedblk3__DOT__unnamedblk4__DOT__state = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> unnamedblk5__DOT_____05Fref;
    IData/*27:0*/ unnamedblk8__DOT_____05Fsaved_recursion_policy;
    unnamedblk8__DOT_____05Fsaved_recursion_policy = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz76> unnamedblk9__DOT_____05Ftmp_rsrc___05F;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> unnamedblk10__DOT__lvalue_ref___05F;
    IData/*27:0*/ unnamedblk10__DOT__unnamedblk11__DOT__prev_pol___05F;
    unnamedblk10__DOT__unnamedblk11__DOT__prev_pol___05F = 0;
    IData/*27:0*/ unnamedblk10__DOT__unnamedblk11__DOT__curr_pol___05F;
    unnamedblk10__DOT__unnamedblk11__DOT__curr_pol___05F = 0;
    IData/*27:0*/ unnamedblk12__DOT__prev_rec___05F;
    unnamedblk12__DOT__prev_rec___05F = 0;
    CData/*0:0*/ unnamedblk12__DOT__unnamedblk13__DOT__rv;
    unnamedblk12__DOT__unnamedblk13__DOT__rv = 0;
    IData/*31:0*/ unnamedblk12__DOT__unnamedblk13__DOT__state;
    unnamedblk12__DOT__unnamedblk13__DOT__state = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> unnamedblk14__DOT_____05Fref;
    IData/*27:0*/ unnamedblk17__DOT_____05Fsaved_recursion_policy;
    unnamedblk17__DOT_____05Fsaved_recursion_policy = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz76> unnamedblk18__DOT_____05Ftmp_rsrc___05F;
    IData/*27:0*/ local_op_type___05F;
    local_op_type___05F = 0;
    VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c> local_rhs___05F;
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
                    VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24)
                               ->__VnoInFunc_get_rhs(vlProcess, vlSymsp, __Vtask_get_rhs__5__Vfuncout);
                }(), __Vtask_get_rhs__5__Vfuncout), local_rhs___05F);
        if ((VL_CAST_DYNAMIC(([&]() {
                            VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24)
                              ->__VnoInFunc_get_rhs(vlProcess, vlSymsp, __Vtask_get_rhs__6__Vfuncout);
                        }(), __Vtask_get_rhs__6__Vfuncout), local_rsrc___05F) 
             && (VlNull{} != local_rsrc___05F))) {
            VL_NULL_CHECK(local_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24)->__VnoInFunc_get_name(vlSymsp, __Vtask_get_name__7__Vfuncout);
            local_rsrc_name___05F = __Vtask_get_name__7__Vfuncout;
        }
        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24)->__VnoInFunc_get_op_type(vlProcess, vlSymsp, __Vtask_get_op_type__8__Vfuncout);
        local_op_type___05F = __Vtask_get_op_type__8__Vfuncout;
        if ((0x00000010U == local_op_type___05F)) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__9__Vfuncout);
                                    }(), __Vtask_get_policy__9__Vfuncout), ___05Flocal_printer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cntxt.svh:24: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24, "");
            }
        } else if ((4U == local_op_type___05F)) {
            if ((VlNull{} == local_rhs___05F)) {
                goto __Vlabel0;
            }
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__10__Vfuncout);
                                    }(), __Vtask_get_policy__10__Vfuncout), ___05Flocal_comparer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cntxt.svh:24: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24, "");
            }
        } else if ((0x00000040U == local_op_type___05F)) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__11__Vfuncout);
                                    }(), __Vtask_get_policy__11__Vfuncout), ___05Flocal_recorder___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cntxt.svh:24: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24, "");
            }
        } else if (((0x00000100U == local_op_type___05F) 
                    || (0x00000400U == local_op_type___05F))) {
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__12__Vfuncout);
                                    }(), __Vtask_get_policy__12__Vfuncout), ___05Flocal_packer___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cntxt.svh:24: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24, "");
            }
        } else if ((1U == local_op_type___05F)) {
            if ((VlNull{} == local_rhs___05F)) {
                goto __Vlabel0;
            }
            if (VL_UNLIKELY(((! VL_CAST_DYNAMIC(([&]() {
                                        VL_NULL_CHECK(___05Flocal_op___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24)
                                                 ->__VnoInFunc_get_policy(vlProcess, vlSymsp, __Vtask_get_policy__13__Vfuncout);
                                    }(), __Vtask_get_policy__13__Vfuncout), ___05Flocal_copier___05F))))) {
                VL_WRITEF_NX("[%0t] %%Error: uvme_fifo_cntxt.svh:24: Assertion failed in %Nuvme_fifo_pkg.uvme_fifo_cntxt_c.__m_uvm_execute_field_op: '$cast' failed.\n",0,
                             64,VL_TIME_UNITED_Q(1000),
                             -9,vlSymsp->name());
                VL_STOP_MT("/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 24, "");
            }
        } else if ((0x00000800U == local_op_type___05F)) {
            if ((VlNull{} == local_rsrc___05F)) {
                goto __Vlabel0;
            }
        } else {
            goto __Vlabel0;
        }
        if ((1U == local_op_type___05F)) {
            if ((this->__PVT__write_cntxt != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                 ->__PVT__write_cntxt)) {
                if (((VlNull{} == VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                      ->__PVT__write_cntxt) || (0x00040000U 
                                                == 
                                                ([&]() {
                                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                 ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__14__Vfuncout);
                                }(), __Vtask_get_recursion_policy__14__Vfuncout)))) {
                    this->__PVT__write_cntxt = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                        ->__PVT__write_cntxt;
                } else if (((1U & (~ (0U != ([&]() {
                                            VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                             ->__VnoInFunc_get_first_copy(vlSymsp, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                          ->__PVT__write_cntxt, unnamedblk1__DOT__lvalue_ref___05F, __Vtask_get_first_copy__15__Vfuncout);
                                        }(), __Vtask_get_first_copy__15__Vfuncout)))) 
                            || (! VL_CAST_DYNAMIC(unnamedblk1__DOT__lvalue_ref___05F, this->__PVT__write_cntxt)))) {
                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__16__Vfuncout);
                    unnamedblk1__DOT__unnamedblk2__DOT__prev_pol___05F 
                        = __Vtask_get_recursion_policy__16__Vfuncout;
                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__17__Vfuncout);
                    unnamedblk1__DOT__unnamedblk2__DOT__curr_pol___05F 
                        = __Vtask_get_recursion_policy__17__Vfuncout;
                    if ((VlNull{} == this->__PVT__write_cntxt)) {
                        if (((0U == VL_CAST_DYNAMIC(
                                                    ([&]() {
                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                              ->__PVT__write_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                     ->__VnoInFunc_create(vlProcess, vlSymsp, 
                                                                          VL_CVT_PACK_STR_NN(
                                                                                ([&]() {
                                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                              ->__PVT__write_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__VnoInFunc_get_name(vlSymsp, __Vtask_get_name__19__Vfuncout);
                                                            }(), __Vtask_get_name__19__Vfuncout)), __Vtask_create__18__Vfuncout);
                                            }(), __Vtask_create__18__Vfuncout), this->__PVT__write_cntxt)) 
                             || (VlNull{} == this->__PVT__write_cntxt))) {
                            if ((0U != ([&]() {
                                            __Vfunc_uvm_report_enabled__20__id = "UVM/COPY/NULL_CREATE"s;
                                            __Vfunc_uvm_report_enabled__20__severity = 3U;
                                            __Vfunc_uvm_report_enabled__20__verbosity = 0U;
                                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__21__Vfuncout);
                                            vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                                = __Vfunc_get__21__Vfuncout;
                                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                        ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__22__Vfuncout);
                                            vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                                = __Vtask_get_root__22__Vfuncout;
                                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                        ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__20__verbosity, (IData)(__Vfunc_uvm_report_enabled__20__severity), __Vfunc_uvm_report_enabled__20__id, __Vtask_uvm_report_enabled__23__Vfuncout);
                                            __Vfunc_uvm_report_enabled__20__Vfuncout 
                                                = __Vtask_uvm_report_enabled__23__Vfuncout;
                                        }(), __Vfunc_uvm_report_enabled__20__Vfuncout))) {
                                vlSymsp->TOP__uvm_pkg.__VnoInFunc_uvm_report_fatal_TOP__uvm_pkg(vlProcess, vlSymsp, "UVM/COPY/NULL_CREATE"s, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Could not create '"s, 
                                                                                ([&]() {
                                                                        VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__PVT__write_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__25__Vfuncout);
                                                                    }(), __Vtask_get_full_name__25__Vfuncout)), "' of type '"s), 
                                                                                ([&]() {
                                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                              ->__PVT__write_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__26__Vfuncout);
                                                            }(), __Vtask_get_type_name__26__Vfuncout)), "', into '"s), "write_cntxt"s), "'."s)), 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh"s, 0x00000019U, ""s, 1U);
                            }
                        } else {
                            VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_copy_object(vlProcess, vlSymsp, this->__PVT__write_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__PVT__write_cntxt);
                        }
                    } else if ((1U == ([&]() {
                                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                       ->__VnoInFunc_object_copied(vlSymsp, this->__PVT__write_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                   ->__PVT__write_cntxt, unnamedblk1__DOT__unnamedblk2__DOT__curr_pol___05F, __Vtask_object_copied__28__Vfuncout);
                                }(), __Vtask_object_copied__28__Vfuncout))) {
                        if ((0U != ([&]() {
                                        __Vfunc_uvm_report_enabled__29__id = "UVM/COPY/LOOP"s;
                                        __Vfunc_uvm_report_enabled__29__severity = 1U;
                                        __Vfunc_uvm_report_enabled__29__verbosity = 0U;
                                        vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__30__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                            = __Vfunc_get__30__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                    ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__31__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                            = __Vtask_get_root__31__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                    ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__29__verbosity, (IData)(__Vfunc_uvm_report_enabled__29__severity), __Vfunc_uvm_report_enabled__29__id, __Vtask_uvm_report_enabled__32__Vfuncout);
                                        __Vfunc_uvm_report_enabled__29__Vfuncout 
                                            = __Vtask_uvm_report_enabled__32__Vfuncout;
                                    }(), __Vfunc_uvm_report_enabled__29__Vfuncout))) {
                            __Vtask_uvm_report_warning__33__report_enabled_checked = 1U;
                            __Vtask_uvm_report_warning__33__context_name = ""s;
                            __Vtask_uvm_report_warning__33__line = 0x00000019U;
                            __Vtask_uvm_report_warning__33__filename = "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh"s;
                            __Vtask_uvm_report_warning__33__verbosity = 0U;
                            __Vtask_uvm_report_warning__33__message 
                                = VL_CVT_PACK_STR_NN(
                                                     VL_CONCATN_NNN(
                                                                    VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Loop detected in copy operation (LHS:'"s, 
                                                                                ([&]() {
                                                        VL_NULL_CHECK(this->__PVT__write_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__34__Vfuncout);
                                                    }(), __Vtask_get_full_name__34__Vfuncout)), "', RHS:'"s), 
                                                                                ([&]() {
                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                              ->__PVT__write_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__35__Vfuncout);
                                            }(), __Vtask_get_full_name__35__Vfuncout)), "')"s));
                            __Vtask_uvm_report_warning__33__id = "UVM/COPY/LOOP"s;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__36__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs 
                                = __Vfunc_get__36__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 155)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__37__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top 
                                = __Vtask_get_root__37__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 156)->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, __Vtask_uvm_report_warning__33__id, __Vtask_uvm_report_warning__33__message, __Vtask_uvm_report_warning__33__verbosity, __Vtask_uvm_report_warning__33__filename, __Vtask_uvm_report_warning__33__line, __Vtask_uvm_report_warning__33__context_name, (IData)(__Vtask_uvm_report_warning__33__report_enabled_checked));
                        }
                    } else {
                        VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_copy_object(vlProcess, vlSymsp, this->__PVT__write_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__PVT__write_cntxt);
                    }
                }
            }
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__40__Vfuncout);
                                    }(), __Vtask_get_threshold__40__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__41__Vfuncout);
                            }(), __Vtask_get_result__41__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__42__Vfuncout);
                            }(), __Vtask_get_threshold__42__Vfuncout)))) {
                if ((this->__PVT__write_cntxt != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                     ->__PVT__write_cntxt)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__43__Vfuncout);
                    unnamedblk3__DOT__prev_rec___05F 
                        = __Vtask_get_recursion_policy__43__Vfuncout;
                    if ((0x00040000U != ([&]() {
                                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                         ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__44__Vfuncout);
                                }(), __Vtask_get_recursion_policy__44__Vfuncout))) {
                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_object_compared(vlSymsp, this->__PVT__write_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__PVT__write_cntxt, 
                                                                                ([&]() {
                                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__46__Vfuncout);
                                }(), __Vtask_get_recursion_policy__46__Vfuncout), __Vtask_object_compared__45__ret_val, __Vtask_object_compared__45__Vfuncout);
                        unnamedblk3__DOT__unnamedblk4__DOT__rv 
                            = __Vtask_object_compared__45__ret_val;
                        unnamedblk3__DOT__unnamedblk4__DOT__state 
                            = __Vtask_object_compared__45__Vfuncout;
                        if (((2U == unnamedblk3__DOT__unnamedblk4__DOT__state) 
                             & (~ (IData)(unnamedblk3__DOT__unnamedblk4__DOT__rv)))) {
                            VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_print_msg(vlProcess, vlSymsp, "'write_cntxt' miscompared using saved return value"s);
                        } else if ((0U == unnamedblk3__DOT__unnamedblk4__DOT__state)) {
                            VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_compare_object(vlProcess, vlSymsp, "write_cntxt"s, this->__PVT__write_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__PVT__write_cntxt, __Vtask_compare_object__48__Vfuncout);
                        }
                    } else {
                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_compare_object(vlProcess, vlSymsp, "write_cntxt"s, this->__PVT__write_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__PVT__write_cntxt, __Vtask_compare_object__49__Vfuncout);
                    }
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_pack_object_with_meta(vlProcess, vlSymsp, this->__PVT__write_cntxt);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk5__DOT_____05Fref = this->__PVT__write_cntxt;
            __Vtask_unpack_object_with_meta__51__value 
                = unnamedblk5__DOT_____05Fref;
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_unpack_object_with_meta(vlProcess, vlSymsp, __Vtask_unpack_object_with_meta__51__value);
            unnamedblk5__DOT_____05Fref = __Vtask_unpack_object_with_meta__51__value;
            if (((unnamedblk5__DOT_____05Fref != this->__PVT__write_cntxt) 
                 && (! VL_CAST_DYNAMIC(unnamedblk5__DOT_____05Fref, this->__PVT__write_cntxt)))) {
                if ((0U != ([&]() {
                                __Vfunc_uvm_report_enabled__52__id = "UVM/UNPACK_EXT/OBJ_CAST_FAILED"s;
                                __Vfunc_uvm_report_enabled__52__severity = 3U;
                                __Vfunc_uvm_report_enabled__52__verbosity = 0U;
                                vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__53__Vfuncout);
                                vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                    = __Vfunc_get__53__Vfuncout;
                                VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                            ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__54__Vfuncout);
                                vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                    = __Vtask_get_root__54__Vfuncout;
                                VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                            ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__52__verbosity, (IData)(__Vfunc_uvm_report_enabled__52__severity), __Vfunc_uvm_report_enabled__52__id, __Vtask_uvm_report_enabled__55__Vfuncout);
                                __Vfunc_uvm_report_enabled__52__Vfuncout 
                                    = __Vtask_uvm_report_enabled__55__Vfuncout;
                            }(), __Vfunc_uvm_report_enabled__52__Vfuncout))) {
                    vlSymsp->TOP__uvm_pkg.__VnoInFunc_uvm_report_fatal_TOP__uvm_pkg(vlProcess, vlSymsp, "UVM/UNPACK_EXT/OBJ_CAST_FAILED"s, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Could not cast object of type '"s, 
                                                                                ([&]() {
                                                VL_NULL_CHECK(unnamedblk5__DOT_____05Fref, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                                                ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__57__Vfuncout);
                                            }(), __Vtask_get_type_name__57__Vfuncout)), "' into '"s), "LVALUE"s)), 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh"s, 0x00000019U, ""s, 1U);
                }
            }
        } else if ((0x00000040U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_record_object(vlProcess, vlSymsp, "write_cntxt"s, this->__PVT__write_cntxt);
        } else if ((0x00000010U == local_op_type___05F)) {
            if ((0U != ([&]() {
                            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                        ->__VnoInFunc_object_printed(vlSymsp, this->__PVT__write_cntxt, 
                                                     ([&]() {
                                        VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                                      ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__60__Vfuncout);
                                    }(), __Vtask_get_recursion_policy__60__Vfuncout), __Vtask_object_printed__59__Vfuncout);
                        }(), __Vtask_object_printed__59__Vfuncout))) {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__61__Vfuncout);
                unnamedblk8__DOT_____05Fsaved_recursion_policy 
                    = __Vtask_get_recursion_policy__61__Vfuncout;
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_set_recursion_policy(vlSymsp, 0x00040000U);
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_print_object(vlProcess, vlSymsp, "write_cntxt"s, this->__PVT__write_cntxt, 0x2eU);
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_set_recursion_policy(vlSymsp, unnamedblk8__DOT_____05Fsaved_recursion_policy);
            } else {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_print_object(vlProcess, vlSymsp, "write_cntxt"s, this->__PVT__write_cntxt, 0x2eU);
            }
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("write_cntxt"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk9__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    VL_NULL_CHECK(unnamedblk9__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c>{this}, __Vtask_read__66__Vfuncout);
                    local_obj___05F = __Vtask_read__66__Vfuncout;
                }
                if (local_success___05F) {
                    if ((VlNull{} == local_obj___05F)) {
                        this->__PVT__write_cntxt = VlNull{};
                    } else if ((! VL_CAST_DYNAMIC(local_obj___05F, this->__PVT__write_cntxt))) {
                        if ((0U != ([&]() {
                                        __Vfunc_uvm_report_enabled__67__id = "UVM/FIELDS/OBJ_TYPE"s;
                                        __Vfunc_uvm_report_enabled__67__severity = 1U;
                                        __Vfunc_uvm_report_enabled__67__verbosity = 0U;
                                        vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__68__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                            = __Vfunc_get__68__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                    ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__69__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                            = __Vtask_get_root__69__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                    ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__67__verbosity, (IData)(__Vfunc_uvm_report_enabled__67__severity), __Vfunc_uvm_report_enabled__67__id, __Vtask_uvm_report_enabled__70__Vfuncout);
                                        __Vfunc_uvm_report_enabled__67__Vfuncout 
                                            = __Vtask_uvm_report_enabled__70__Vfuncout;
                                    }(), __Vfunc_uvm_report_enabled__67__Vfuncout))) {
                            __Vtask_uvm_report_warning__71__report_enabled_checked = 1U;
                            __Vtask_uvm_report_warning__71__context_name = ""s;
                            __Vtask_uvm_report_warning__71__line = 0x00000019U;
                            __Vtask_uvm_report_warning__71__filename = "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh"s;
                            __Vtask_uvm_report_warning__71__verbosity = 0U;
                            __Vtemp_1 = ([&]() {
                                    this->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vfunc_get_full_name__72__Vfuncout);
                                }(), __Vfunc_get_full_name__72__Vfuncout);
                            __Vtemp_2 = ([&]() {
                                    VL_NULL_CHECK(local_obj___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 25)
                                         ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__73__Vfuncout);
                                }(), __Vtask_get_type_name__73__Vfuncout);
                            __Vtask_uvm_report_warning__71__message 
                                = VL_SFORMATF_N_NX("Can't set field 'write_cntxt' on '%@' with '%@' type",0,
                                                   -1,
                                                   &(__Vtemp_1),
                                                   -1,
                                                   &(__Vtemp_2)) ;
                            __Vtask_uvm_report_warning__71__id = "UVM/FIELDS/OBJ_TYPE"s;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__74__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs 
                                = __Vfunc_get__74__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 155)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__75__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top 
                                = __Vtask_get_root__75__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 156)->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, __Vtask_uvm_report_warning__71__id, __Vtask_uvm_report_warning__71__message, __Vtask_uvm_report_warning__71__verbosity, __Vtask_uvm_report_warning__71__filename, __Vtask_uvm_report_warning__71__line, __Vtask_uvm_report_warning__71__context_name, (IData)(__Vtask_uvm_report_warning__71__report_enabled_checked));
                        }
                    }
                }
            }
        }
        if ((1U == local_op_type___05F)) {
            if ((this->__PVT__read_cntxt != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                 ->__PVT__read_cntxt)) {
                if (((VlNull{} == VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                      ->__PVT__read_cntxt) || (0x00040000U 
                                               == ([&]() {
                                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                   ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__77__Vfuncout);
                                }(), __Vtask_get_recursion_policy__77__Vfuncout)))) {
                    this->__PVT__read_cntxt = VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                        ->__PVT__read_cntxt;
                } else if (((1U & (~ (0U != ([&]() {
                                            VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                             ->__VnoInFunc_get_first_copy(vlSymsp, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                          ->__PVT__read_cntxt, unnamedblk10__DOT__lvalue_ref___05F, __Vtask_get_first_copy__78__Vfuncout);
                                        }(), __Vtask_get_first_copy__78__Vfuncout)))) 
                            || (! VL_CAST_DYNAMIC(unnamedblk10__DOT__lvalue_ref___05F, this->__PVT__read_cntxt)))) {
                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__79__Vfuncout);
                    unnamedblk10__DOT__unnamedblk11__DOT__prev_pol___05F 
                        = __Vtask_get_recursion_policy__79__Vfuncout;
                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__80__Vfuncout);
                    unnamedblk10__DOT__unnamedblk11__DOT__curr_pol___05F 
                        = __Vtask_get_recursion_policy__80__Vfuncout;
                    if ((VlNull{} == this->__PVT__read_cntxt)) {
                        if (((0U == VL_CAST_DYNAMIC(
                                                    ([&]() {
                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                              ->__PVT__read_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                     ->__VnoInFunc_create(vlProcess, vlSymsp, 
                                                                          VL_CVT_PACK_STR_NN(
                                                                                ([&]() {
                                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                              ->__PVT__read_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__VnoInFunc_get_name(vlSymsp, __Vtask_get_name__82__Vfuncout);
                                                            }(), __Vtask_get_name__82__Vfuncout)), __Vtask_create__81__Vfuncout);
                                            }(), __Vtask_create__81__Vfuncout), this->__PVT__read_cntxt)) 
                             || (VlNull{} == this->__PVT__read_cntxt))) {
                            if ((0U != ([&]() {
                                            __Vfunc_uvm_report_enabled__83__id = "UVM/COPY/NULL_CREATE"s;
                                            __Vfunc_uvm_report_enabled__83__severity = 3U;
                                            __Vfunc_uvm_report_enabled__83__verbosity = 0U;
                                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__84__Vfuncout);
                                            vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                                = __Vfunc_get__84__Vfuncout;
                                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                        ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__85__Vfuncout);
                                            vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                                = __Vtask_get_root__85__Vfuncout;
                                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                        ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__83__verbosity, (IData)(__Vfunc_uvm_report_enabled__83__severity), __Vfunc_uvm_report_enabled__83__id, __Vtask_uvm_report_enabled__86__Vfuncout);
                                            __Vfunc_uvm_report_enabled__83__Vfuncout 
                                                = __Vtask_uvm_report_enabled__86__Vfuncout;
                                        }(), __Vfunc_uvm_report_enabled__83__Vfuncout))) {
                                vlSymsp->TOP__uvm_pkg.__VnoInFunc_uvm_report_fatal_TOP__uvm_pkg(vlProcess, vlSymsp, "UVM/COPY/NULL_CREATE"s, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Could not create '"s, 
                                                                                ([&]() {
                                                                        VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__PVT__read_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__88__Vfuncout);
                                                                    }(), __Vtask_get_full_name__88__Vfuncout)), "' of type '"s), 
                                                                                ([&]() {
                                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                              ->__PVT__read_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__89__Vfuncout);
                                                            }(), __Vtask_get_type_name__89__Vfuncout)), "', into '"s), "read_cntxt"s), "'."s)), 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh"s, 0x0000001aU, ""s, 1U);
                            }
                        } else {
                            VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_copy_object(vlProcess, vlSymsp, this->__PVT__read_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__PVT__read_cntxt);
                        }
                    } else if ((1U == ([&]() {
                                    VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                       ->__VnoInFunc_object_copied(vlSymsp, this->__PVT__read_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                   ->__PVT__read_cntxt, unnamedblk10__DOT__unnamedblk11__DOT__curr_pol___05F, __Vtask_object_copied__91__Vfuncout);
                                }(), __Vtask_object_copied__91__Vfuncout))) {
                        if ((0U != ([&]() {
                                        __Vfunc_uvm_report_enabled__92__id = "UVM/COPY/LOOP"s;
                                        __Vfunc_uvm_report_enabled__92__severity = 1U;
                                        __Vfunc_uvm_report_enabled__92__verbosity = 0U;
                                        vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__93__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                            = __Vfunc_get__93__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                    ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__94__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                            = __Vtask_get_root__94__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                    ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__92__verbosity, (IData)(__Vfunc_uvm_report_enabled__92__severity), __Vfunc_uvm_report_enabled__92__id, __Vtask_uvm_report_enabled__95__Vfuncout);
                                        __Vfunc_uvm_report_enabled__92__Vfuncout 
                                            = __Vtask_uvm_report_enabled__95__Vfuncout;
                                    }(), __Vfunc_uvm_report_enabled__92__Vfuncout))) {
                            __Vtask_uvm_report_warning__96__report_enabled_checked = 1U;
                            __Vtask_uvm_report_warning__96__context_name = ""s;
                            __Vtask_uvm_report_warning__96__line = 0x0000001aU;
                            __Vtask_uvm_report_warning__96__filename = "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh"s;
                            __Vtask_uvm_report_warning__96__verbosity = 0U;
                            __Vtask_uvm_report_warning__96__message 
                                = VL_CVT_PACK_STR_NN(
                                                     VL_CONCATN_NNN(
                                                                    VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Loop detected in copy operation (LHS:'"s, 
                                                                                ([&]() {
                                                        VL_NULL_CHECK(this->__PVT__read_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__97__Vfuncout);
                                                    }(), __Vtask_get_full_name__97__Vfuncout)), "', RHS:'"s), 
                                                                                ([&]() {
                                                VL_NULL_CHECK(VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                              ->__PVT__read_cntxt, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vtask_get_full_name__98__Vfuncout);
                                            }(), __Vtask_get_full_name__98__Vfuncout)), "')"s));
                            __Vtask_uvm_report_warning__96__id = "UVM/COPY/LOOP"s;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__99__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs 
                                = __Vfunc_get__99__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 155)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__100__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top 
                                = __Vtask_get_root__100__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 156)->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, __Vtask_uvm_report_warning__96__id, __Vtask_uvm_report_warning__96__message, __Vtask_uvm_report_warning__96__verbosity, __Vtask_uvm_report_warning__96__filename, __Vtask_uvm_report_warning__96__line, __Vtask_uvm_report_warning__96__context_name, (IData)(__Vtask_uvm_report_warning__96__report_enabled_checked));
                        }
                    } else {
                        VL_NULL_CHECK(___05Flocal_copier___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_copy_object(vlProcess, vlSymsp, this->__PVT__read_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__PVT__read_cntxt);
                    }
                }
            }
        } else if ((4U == local_op_type___05F)) {
            if (((1U & (~ (0U != ([&]() {
                                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                  ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__103__Vfuncout);
                                    }(), __Vtask_get_threshold__103__Vfuncout)))) 
                 || (([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                      ->__VnoInFunc_get_result(vlSymsp, __Vtask_get_result__104__Vfuncout);
                            }(), __Vtask_get_result__104__Vfuncout) 
                     < ([&]() {
                                VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                        ->__VnoInFunc_get_threshold(vlSymsp, __Vtask_get_threshold__105__Vfuncout);
                            }(), __Vtask_get_threshold__105__Vfuncout)))) {
                if ((this->__PVT__read_cntxt != VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                     ->__PVT__read_cntxt)) {
                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__106__Vfuncout);
                    unnamedblk12__DOT__prev_rec___05F 
                        = __Vtask_get_recursion_policy__106__Vfuncout;
                    if ((0x00040000U != ([&]() {
                                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                         ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__107__Vfuncout);
                                }(), __Vtask_get_recursion_policy__107__Vfuncout))) {
                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_object_compared(vlSymsp, this->__PVT__read_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__PVT__read_cntxt, 
                                                                                ([&]() {
                                    VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__109__Vfuncout);
                                }(), __Vtask_get_recursion_policy__109__Vfuncout), __Vtask_object_compared__108__ret_val, __Vtask_object_compared__108__Vfuncout);
                        unnamedblk12__DOT__unnamedblk13__DOT__rv 
                            = __Vtask_object_compared__108__ret_val;
                        unnamedblk12__DOT__unnamedblk13__DOT__state 
                            = __Vtask_object_compared__108__Vfuncout;
                        if (((2U == unnamedblk12__DOT__unnamedblk13__DOT__state) 
                             & (~ (IData)(unnamedblk12__DOT__unnamedblk13__DOT__rv)))) {
                            VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_print_msg(vlProcess, vlSymsp, "'read_cntxt' miscompared using saved return value"s);
                        } else if ((0U == unnamedblk12__DOT__unnamedblk13__DOT__state)) {
                            VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_compare_object(vlProcess, vlSymsp, "read_cntxt"s, this->__PVT__read_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__PVT__read_cntxt, __Vtask_compare_object__111__Vfuncout);
                        }
                    } else {
                        VL_NULL_CHECK(___05Flocal_comparer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_compare_object(vlProcess, vlSymsp, "read_cntxt"s, this->__PVT__read_cntxt, VL_NULL_CHECK(local_rhs___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__PVT__read_cntxt, __Vtask_compare_object__112__Vfuncout);
                    }
                }
            }
        } else if ((0x00000100U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_pack_object_with_meta(vlProcess, vlSymsp, this->__PVT__read_cntxt);
        } else if ((0x00000400U == local_op_type___05F)) {
            unnamedblk14__DOT_____05Fref = this->__PVT__read_cntxt;
            __Vtask_unpack_object_with_meta__114__value 
                = unnamedblk14__DOT_____05Fref;
            VL_NULL_CHECK(___05Flocal_packer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_unpack_object_with_meta(vlProcess, vlSymsp, __Vtask_unpack_object_with_meta__114__value);
            unnamedblk14__DOT_____05Fref = __Vtask_unpack_object_with_meta__114__value;
            if (((unnamedblk14__DOT_____05Fref != this->__PVT__read_cntxt) 
                 && (! VL_CAST_DYNAMIC(unnamedblk14__DOT_____05Fref, this->__PVT__read_cntxt)))) {
                if ((0U != ([&]() {
                                __Vfunc_uvm_report_enabled__115__id = "UVM/UNPACK_EXT/OBJ_CAST_FAILED"s;
                                __Vfunc_uvm_report_enabled__115__severity = 3U;
                                __Vfunc_uvm_report_enabled__115__verbosity = 0U;
                                vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__116__Vfuncout);
                                vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                    = __Vfunc_get__116__Vfuncout;
                                VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                            ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__117__Vfuncout);
                                vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                    = __Vtask_get_root__117__Vfuncout;
                                VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                            ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__115__verbosity, (IData)(__Vfunc_uvm_report_enabled__115__severity), __Vfunc_uvm_report_enabled__115__id, __Vtask_uvm_report_enabled__118__Vfuncout);
                                __Vfunc_uvm_report_enabled__115__Vfuncout 
                                    = __Vtask_uvm_report_enabled__118__Vfuncout;
                            }(), __Vfunc_uvm_report_enabled__115__Vfuncout))) {
                    vlSymsp->TOP__uvm_pkg.__VnoInFunc_uvm_report_fatal_TOP__uvm_pkg(vlProcess, vlSymsp, "UVM/UNPACK_EXT/OBJ_CAST_FAILED"s, 
                                                                                VL_CVT_PACK_STR_NN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN(
                                                                                VL_CONCATN_NNN("Could not cast object of type '"s, 
                                                                                ([&]() {
                                                VL_NULL_CHECK(unnamedblk14__DOT_____05Fref, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                                                ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__120__Vfuncout);
                                            }(), __Vtask_get_type_name__120__Vfuncout)), "' into '"s), "LVALUE"s)), 0U, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh"s, 0x0000001aU, ""s, 1U);
                }
            }
        } else if ((0x00000040U == local_op_type___05F)) {
            VL_NULL_CHECK(___05Flocal_recorder___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_record_object(vlProcess, vlSymsp, "read_cntxt"s, this->__PVT__read_cntxt);
        } else if ((0x00000010U == local_op_type___05F)) {
            if ((0U != ([&]() {
                            VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                        ->__VnoInFunc_object_printed(vlSymsp, this->__PVT__read_cntxt, 
                                                     ([&]() {
                                        VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                                      ->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__123__Vfuncout);
                                    }(), __Vtask_get_recursion_policy__123__Vfuncout), __Vtask_object_printed__122__Vfuncout);
                        }(), __Vtask_object_printed__122__Vfuncout))) {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_get_recursion_policy(vlSymsp, __Vtask_get_recursion_policy__124__Vfuncout);
                unnamedblk17__DOT_____05Fsaved_recursion_policy 
                    = __Vtask_get_recursion_policy__124__Vfuncout;
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_set_recursion_policy(vlSymsp, 0x00040000U);
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_print_object(vlProcess, vlSymsp, "read_cntxt"s, this->__PVT__read_cntxt, 0x2eU);
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_set_recursion_policy(vlSymsp, unnamedblk17__DOT_____05Fsaved_recursion_policy);
            } else {
                VL_NULL_CHECK(___05Flocal_printer___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_print_object(vlProcess, vlSymsp, "read_cntxt"s, this->__PVT__read_cntxt, 0x2eU);
            }
        } else if ((0x00000800U == local_op_type___05F)) {
            if (("read_cntxt"s == local_rsrc_name___05F)) {
                local_success___05F = (1U & VL_CAST_DYNAMIC(local_rsrc___05F, unnamedblk18__DOT_____05Ftmp_rsrc___05F));
                if (local_success___05F) {
                    VL_NULL_CHECK(unnamedblk18__DOT_____05Ftmp_rsrc___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)->__VnoInFunc_read(vlProcess, vlSymsp, 
                                                                                VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c>{this}, __Vtask_read__129__Vfuncout);
                    local_obj___05F = __Vtask_read__129__Vfuncout;
                }
                if (local_success___05F) {
                    if ((VlNull{} == local_obj___05F)) {
                        this->__PVT__read_cntxt = VlNull{};
                    } else if ((! VL_CAST_DYNAMIC(local_obj___05F, this->__PVT__read_cntxt))) {
                        if ((0U != ([&]() {
                                        __Vfunc_uvm_report_enabled__130__id = "UVM/FIELDS/OBJ_TYPE"s;
                                        __Vfunc_uvm_report_enabled__130__severity = 1U;
                                        __Vfunc_uvm_report_enabled__130__verbosity = 0U;
                                        vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__131__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs 
                                            = __Vfunc_get__131__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 89)
                                    ->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__132__Vfuncout);
                                        vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top 
                                            = __Vtask_get_root__132__Vfuncout;
                                        VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.uvm_report_enabled__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 90)
                                    ->__VnoInFunc_uvm_report_enabled(vlProcess, vlSymsp, __Vfunc_uvm_report_enabled__130__verbosity, (IData)(__Vfunc_uvm_report_enabled__130__severity), __Vfunc_uvm_report_enabled__130__id, __Vtask_uvm_report_enabled__133__Vfuncout);
                                        __Vfunc_uvm_report_enabled__130__Vfuncout 
                                            = __Vtask_uvm_report_enabled__133__Vfuncout;
                                    }(), __Vfunc_uvm_report_enabled__130__Vfuncout))) {
                            __Vtask_uvm_report_warning__134__report_enabled_checked = 1U;
                            __Vtask_uvm_report_warning__134__context_name = ""s;
                            __Vtask_uvm_report_warning__134__line = 0x0000001aU;
                            __Vtask_uvm_report_warning__134__filename = "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh"s;
                            __Vtask_uvm_report_warning__134__verbosity = 0U;
                            __Vtemp_3 = ([&]() {
                                    this->__VnoInFunc_get_full_name(vlProcess, vlSymsp, __Vfunc_get_full_name__135__Vfuncout);
                                }(), __Vfunc_get_full_name__135__Vfuncout);
                            __Vtemp_4 = ([&]() {
                                    VL_NULL_CHECK(local_obj___05F, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../uvm_tests/uvm_test_cvv/uvme/uvme_fifo_cntxt.svh", 26)
                                         ->__VnoInFunc_get_type_name(vlSymsp, __Vtask_get_type_name__136__Vfuncout);
                                }(), __Vtask_get_type_name__136__Vfuncout);
                            __Vtask_uvm_report_warning__134__message 
                                = VL_SFORMATF_N_NX("Can't set field 'read_cntxt' on '%@' with '%@' type",0,
                                                   -1,
                                                   &(__Vtemp_3),
                                                   -1,
                                                   &(__Vtemp_4)) ;
                            __Vtask_uvm_report_warning__134__id = "UVM/FIELDS/OBJ_TYPE"s;
                            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__137__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs 
                                = __Vfunc_get__137__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 155)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__138__Vfuncout);
                            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top 
                                = __Vtask_get_root__138__Vfuncout;
                            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 156)->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, __Vtask_uvm_report_warning__134__id, __Vtask_uvm_report_warning__134__message, __Vtask_uvm_report_warning__134__verbosity, __Vtask_uvm_report_warning__134__filename, __Vtask_uvm_report_warning__134__line, __Vtask_uvm_report_warning__134__context_name, (IData)(__Vtask_uvm_report_warning__134__report_enabled_checked));
                        }
                    }
                }
            }
        }
        __Vlabel0: ;
    }
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_object(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::new\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c> __Vfunc_create__141__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvma_wr_rd_pkg__03a__03auvma_wr_rd_cntxt_c> __Vfunc_create__142__Vfuncout;
    // Body
    _ctor_var_reset(vlSymsp);
    ;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi85__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "write_cntxt"s, VlNull{}, ""s, __Vfunc_create__141__Vfuncout);
    this->__PVT__write_cntxt = __Vfunc_create__141__Vfuncout;
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__pi85__Vclpkg.__VnoInFunc_create(vlProcess, vlSymsp, "read_cntxt"s, VlNull{}, ""s, __Vfunc_create__142__Vfuncout);
    this->__PVT__read_cntxt = __Vfunc_create__142__Vfuncout;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__144__Vfuncout;
    __Vfunc___VBasicRand__144__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__144__Vfuncout);
            }(), __Vfunc___VBasicRand__144__Vfuncout));
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
    __PVT__wr_vif = nullptr;
    __PVT__rd_vif = nullptr;
}

uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::~uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                                    uvmt_fifo_tb_uvme_fifo_pkg__03a__03auvme_fifo_cntxt_c::to_string_middle\n"); );
    // Body
    std::string out;
    out += "wr_vif:" + VL_TO_STRING(__PVT__wr_vif);
    out += ", rd_vif:" + VL_TO_STRING(__PVT__rd_vif);
    out += ", write_cntxt:" + VL_TO_STRING(__PVT__write_cntxt);
    out += ", read_cntxt:" + VL_TO_STRING(__PVT__read_cntxt);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::to_string_middle();
    return (out);
}
