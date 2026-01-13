// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See uvmt_fifo_tb.h for the primary calling header

#include "uvmt_fifo_tb__pch.h"

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10__Vclpkg::__VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz60> &get_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10__Vclpkg::__VnoInFunc_get_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz60> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__Tz60__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10__Vclpkg::__VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10__Vclpkg::__VnoInFunc_type_name\n"); );
    // Body
    type_name__Vfuncrtn = "uvm_pool"s;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10__Vclpkg::__VnoInFunc_get_global_pool(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10> &get_global_pool__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10__Vclpkg::__VnoInFunc_get_global_pool\n"); );
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    if ((VlNull{} == this->__PVT__m_global_pool)) {
        this->__PVT__m_global_pool = VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10, vlProcess, vlSymsp, "pool"s);
    }
    get_global_pool__Vfuncrtn = this->__PVT__m_global_pool;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10__Vclpkg::__VnoInFunc_get_global(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3> &get_global__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10__Vclpkg::__VnoInFunc_get_global\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10> __Vfunc_get_global_pool__2__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3> __Vtask_get__3__Vfuncout;
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10> gpool;
    this->__VnoInFunc_get_global_pool(vlSymsp, __Vfunc_get_global_pool__2__Vfuncout);
    gpool = __Vfunc_get_global_pool__2__Vfuncout;
    VL_NULL_CHECK(gpool, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_pool.svh", 80)->__VnoInFunc_get(vlSymsp, key, __Vtask_get__3__Vfuncout);
    get_global__Vfuncrtn = __Vtask_get__3__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_get_object_type\n"); );
    // Locals
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_registry__Tz60> __Vfunc_get__0__Vfuncout;
    // Body
    vlSymsp->TOP__uvm_pkg__03a__03auvm_object_registry__Tz60__Vclpkg.__VnoInFunc_get(vlSymsp, __Vfunc_get__0__Vfuncout);
    get_object_type__Vfuncrtn = __Vfunc_get__0__Vfuncout;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_create(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> &create__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_create\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10> tmp;
    tmp = ((""s == name) ? VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10, vlProcess, vlSymsp, ""s)
            : VL_NEW(uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10, vlProcess, vlSymsp, name));
    create__Vfuncrtn = tmp;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_get_type_name\n"); );
    // Body
    get_type_name__Vfuncrtn = "uvm_pool"s;
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name)
    : uvmt_fifo_tb_uvm_pkg__03a__03auvm_object(vlProcess, vlSymsp, name) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::new\n"); );
    // Body
    _ctor_var_reset(vlSymsp);
    ;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_get(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3> &get__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_get\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3> unnamedblk1__DOT__default_value;
    if ((! this->__PVT__pool.exists(key))) {
        this->__PVT__pool.at(key) = unnamedblk1__DOT__default_value;
    }
    get__Vfuncrtn = this->__PVT__pool.at(key);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_add(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz3> item) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_add\n"); );
    // Body
    this->__PVT__pool.at(key) = item;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_num(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &num__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_num\n"); );
    // Body
    num__Vfuncrtn = this->__PVT__pool.size();
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_delete(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_delete\n"); );
    // Locals
    IData/*31:0*/ __Vfunc_exists__4__Vfuncout;
    __Vfunc_exists__4__Vfuncout = 0;
    std::string __Vtask_uvm_report_warning__5__id;
    std::string __Vtask_uvm_report_warning__5__message;
    IData/*31:0*/ __Vtask_uvm_report_warning__5__verbosity;
    __Vtask_uvm_report_warning__5__verbosity = 0;
    std::string __Vtask_uvm_report_warning__5__filename;
    IData/*31:0*/ __Vtask_uvm_report_warning__5__line;
    __Vtask_uvm_report_warning__5__line = 0;
    std::string __Vtask_uvm_report_warning__5__context_name;
    CData/*0:0*/ __Vtask_uvm_report_warning__5__report_enabled_checked;
    __Vtask_uvm_report_warning__5__report_enabled_checked = 0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t> __Vfunc_get__6__Vfuncout;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_root> __Vtask_get_root__7__Vfuncout;
    // Body
    VlProcessRef vlProcess = std::make_shared<VlProcess>();
    {
        if ((1U & (~ (0U != ([&]() {
                                this->__VnoInFunc_exists(vlSymsp, key, __Vfunc_exists__4__Vfuncout);
                            }(), __Vfunc_exists__4__Vfuncout))))) {
            __Vtask_uvm_report_warning__5__report_enabled_checked = 0U;
            __Vtask_uvm_report_warning__5__context_name = ""s;
            __Vtask_uvm_report_warning__5__line = 0U;
            __Vtask_uvm_report_warning__5__filename = ""s;
            __Vtask_uvm_report_warning__5__verbosity = 0x000000c8U;
            __Vtask_uvm_report_warning__5__message = "delete: pool key doesn't exist. Ignoring delete request"s;
            __Vtask_uvm_report_warning__5__id = "POOLDEL"s;
            vlSymsp->TOP__uvm_pkg__03a__03auvm_coreservice_t__Vclpkg.__VnoInFunc_get(vlProcess, vlSymsp, __Vfunc_get__6__Vfuncout);
            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs 
                = __Vfunc_get__6__Vfuncout;
            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__cs, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 155)->__VnoInFunc_get_root(vlProcess, vlSymsp, __Vtask_get_root__7__Vfuncout);
            vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top 
                = __Vtask_get_root__7__Vfuncout;
            VL_NULL_CHECK(vlSymsp->TOP__uvm_pkg.__PVT__uvm_report_warning__Vstatic__top, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_globals.svh", 156)->__VnoInFunc_uvm_report_warning(vlProcess, vlSymsp, __Vtask_uvm_report_warning__5__id, __Vtask_uvm_report_warning__5__message, __Vtask_uvm_report_warning__5__verbosity, __Vtask_uvm_report_warning__5__filename, __Vtask_uvm_report_warning__5__line, __Vtask_uvm_report_warning__5__context_name, (IData)(__Vtask_uvm_report_warning__5__report_enabled_checked));
            goto __Vlabel0;
        }
        this->__PVT__pool.erase(key);
        __Vlabel0: ;
    }
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_exists(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string key, IData/*31:0*/ &exists__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_exists\n"); );
    // Body
    exists__Vfuncrtn = this->__PVT__pool.exists(key);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_first(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &key, IData/*31:0*/ &first__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_first\n"); );
    // Body
    first__Vfuncrtn = this->__PVT__pool.first(key);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_last(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &key, IData/*31:0*/ &last__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_last\n"); );
    // Body
    last__Vfuncrtn = this->__PVT__pool.last(key);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_next(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &key, IData/*31:0*/ &next__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_next\n"); );
    // Body
    next__Vfuncrtn = this->__PVT__pool.next(key);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_prev(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &key, IData/*31:0*/ &prev__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_prev\n"); );
    // Body
    prev__Vfuncrtn = this->__PVT__pool.prev(key);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_do_copy(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object> rhs) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_do_copy\n"); );
    // Body
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10> p;
    std::string key;
    {
        uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::__VnoInFunc_do_copy(vlProcess, vlSymsp, rhs);
        if (((VlNull{} == rhs) || (! VL_CAST_DYNAMIC(rhs, p)))) {
            goto __Vlabel0;
        }
        this->__PVT__pool = VL_NULL_CHECK(p, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_pool.svh", 215)
            ->__PVT__pool;
        __Vlabel0: ;
    }
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_do_print\n"); );
    // Locals
    std::string __Vtemp_1;
    // Body
    std::string v;
    IData/*31:0*/ cnt;
    cnt = 0;
    std::string item;
    std::string key;
    VL_NULL_CHECK(printer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_pool.svh", 223)->__VnoInFunc_print_array_header(vlProcess, vlSymsp, "pool"s, this->__PVT__pool.size(), "aa_object_string"s, 0x2eU);
    if ((0U != this->__PVT__pool.first(key))) {
        do {
            item = VL_SFORMATF_N_NX("%0d",0,32,cnt) ;
            item = VL_CONCATN_NNN(VL_CONCATN_NNN("[-key"s, item), "--]"s);
            __Vtemp_1 = VL_TO_STRING(this->__PVT__pool
                                     .at(key));
            VL_SFORMAT_NX(64,v,"%@",0,-1,&(__Vtemp_1));
            VL_NULL_CHECK(printer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_pool.svh", 229)->__VnoInFunc_print_generic(vlProcess, vlSymsp, item, ""s, 0xffffffffU, v, 0x5bU);
        } while ((0U != this->__PVT__pool.next(key)));
    }
    VL_NULL_CHECK(printer, "/home/yilou/Desktop/OSVISE/planvtech/PlanV_Verilator_Feature_Tests/planv_tests/uvm_tests/uvm_test_cvv/sim/veri-sim/../../../../../uvm_lib/uvm-antmicro-deprecatedApi/src/base/uvm_pool.svh", 232)->__VnoInFunc_print_array_footer(vlSymsp, 0U);
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc_randomize\n"); );
    // Locals
    IData/*31:0*/ __Vfunc___VBasicRand__14__Vfuncout;
    __Vfunc___VBasicRand__14__Vfuncout = 0;
    // Body
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.clearConstraints();
    this->__VnoInFunc___Vsetup_constraints(vlSymsp);
    randomize__Vfuncrtn = uvmt_fifo_tb_uvm_pkg__03a__03auvm_void::__PVT__constraint.next(__Vm_rng);
    randomize__Vfuncrtn = (randomize__Vfuncrtn & ([&]() {
                this->__VnoInFunc___VBasicRand(vlSymsp, __Vfunc___VBasicRand__14__Vfuncout);
            }(), __Vfunc___VBasicRand__14__Vfuncout));
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc___Vsetup_constraints\n"); );
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::__VnoInFunc___VBasicRand\n"); );
    // Body
    __VBasicRand__Vfuncrtn = 1U;
}

void uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::_ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::_ctor_var_reset\n"); );
    // Body
    (void)vlSymsp;  // Prevent unused variable warning
}

uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::~uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10() {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::~\n"); );
}

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10>& obj) {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::VL_TO_STRING\n"); );
    // Body
    return (obj ? obj->to_string() : "null");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::to_string() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::to_string\n"); );
    // Body
    return ("'{"s + to_string_middle() + "}");
}

std::string uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::to_string_middle() const {
    VL_DEBUG_IF(VL_DBG_MSGF("+                  uvmt_fifo_tb_uvm_pkg__03a__03auvm_pool__Tz5_TBz10::to_string_middle\n"); );
    // Body
    std::string out;
    out += "pool:" + VL_TO_STRING(__PVT__pool);
    out += ", "+ uvmt_fifo_tb_uvm_pkg__03a__03auvm_object::to_string_middle();
    return (out);
}
