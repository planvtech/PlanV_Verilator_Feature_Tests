// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SEQUENCE_BASE__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SEQUENCE_BASE__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_abstract_object_registry__pi7;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_to_lock_dap__Tz19;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_to_lock_dap__Tz4;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base__Vclpkg final {
  public:

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
    void __VnoInFunc_get_type(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_abstract_object_registry__pi7> &get_type__Vfuncrtn);
    void __VnoInFunc_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &type_name__Vfuncrtn);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__response_queue_error_report_enabled;
    CData/*0:0*/ __PVT__do_not_randomize;
    CData/*0:0*/ __PVT__m_use_response_handler;
    CData/*0:0*/ __PVT__is_rel_default;
    CData/*0:0*/ __PVT__wait_rel_default;
    CData/*0:0*/ __Vtrigprevexpr_h6dd9d6e8__0;
    CData/*0:0*/ __Vtrigprevexpr_he247a826__0;
    CData/*0:0*/ __Vtrigprevexpr_hce0d2f30__0;
    IData/*31:0*/ __PVT__m_sequence_state;
    IData/*31:0*/ __PVT__m_next_transaction_id;
    IData/*31:0*/ __PVT__m_priority;
    IData/*31:0*/ __PVT__m_wait_for_grant_semaphore;
    IData/*31:0*/ __PVT__response_queue_depth;
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base>, CData/*0:0*/> __PVT__children_array;
    VlAssocArray<IData/*31:0*/, IData/*31:0*/> __PVT__m_sqr_seq_ids;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_recorder> __PVT__m_tr_recorder;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item>> __PVT__response_queue;
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __PVT__m_sequence_process;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_to_lock_dap__Tz4> __PVT__m_automatic_phase_objection_dap;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_get_to_lock_dap__Tz19> __PVT__m_starting_phase_dap;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_body(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_clean_exit_sequence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_clear_response_queue(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_create_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> type_var, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base> l_sequencer, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &create_item__Vfuncrtn);
    virtual void __VnoInFunc_do_kill(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual VlCoroutine __VnoInFunc_finish_item(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> item, IData/*31:0*/ set_priority);
    void __VnoInFunc_get_automatic_phase_objection(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &get_automatic_phase_objection__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_get_base_response(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> &response, IData/*31:0*/ transaction_id);
    virtual void __VnoInFunc_get_object_type(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper> &get_object_type__Vfuncrtn);
    void __VnoInFunc_get_priority(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_priority__Vfuncrtn);
    virtual void __VnoInFunc_get_randomize_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &get_randomize_enabled__Vfuncrtn);
    void __VnoInFunc_get_response_queue_depth(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_response_queue_depth__Vfuncrtn);
    void __VnoInFunc_get_response_queue_error_report_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &get_response_queue_error_report_enabled__Vfuncrtn);
    void __VnoInFunc_get_sequence_state(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_sequence_state__Vfuncrtn);
    void __VnoInFunc_get_starting_phase(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> &get_starting_phase__Vfuncrtn);
    void __VnoInFunc_get_tr_handle(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_tr_handle__Vfuncrtn);
    virtual void __VnoInFunc_get_type_name(uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &get_type_name__Vfuncrtn);
    void __VnoInFunc_get_use_response_handler(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &get_use_response_handler__Vfuncrtn);
    VlCoroutine __VnoInFunc_grab(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base> sequencer);
    void __VnoInFunc_has_lock(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &has_lock__Vfuncrtn);
    void __VnoInFunc_is_blocked(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_blocked__Vfuncrtn);
    virtual void __VnoInFunc_is_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_item__Vfuncrtn);
    virtual void __VnoInFunc_is_relevant(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_relevant__Vfuncrtn);
    void __VnoInFunc_kill(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_lock(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base> sequencer);
    void __VnoInFunc_m_get_sqr_sequence_id(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ sequencer_id, CData/*0:0*/ update_sequence_id, IData/*31:0*/ &m_get_sqr_sequence_id__Vfuncrtn);
    void __VnoInFunc_m_init_phase_daps(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ create);
    void __VnoInFunc_m_kill(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_m_safe_drop_starting_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string description, IData/*31:0*/ count);
    void __VnoInFunc_m_safe_raise_starting_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string description, IData/*31:0*/ count);
    void __VnoInFunc_m_set_sqr_sequence_id(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ sequencer_id, IData/*31:0*/ sequence_id);
    virtual void __VnoInFunc_mid_do(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> this_item);
    virtual void __VnoInFunc_post_body(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_post_do(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> this_item);
    virtual void __VnoInFunc_post_start(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_pre_body(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_pre_do(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ is_item);
    virtual void __VnoInFunc_pre_start(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_put_base_response(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> response);
    virtual void __VnoInFunc_put_response(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> response_item);
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    virtual void __VnoInFunc_response_handler(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> response);
    virtual void __VnoInFunc_send_request(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> request, CData/*0:0*/ rerandomize);
    void __VnoInFunc_set_automatic_phase_objection(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ value);
    void __VnoInFunc_set_priority(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ value);
    virtual void __VnoInFunc_set_randomize_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ enable);
    void __VnoInFunc_set_response_queue_depth(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ value);
    void __VnoInFunc_set_response_queue_error_report_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ value);
    void __VnoInFunc_set_starting_phase(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual VlCoroutine __VnoInFunc_start(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base> sequencer, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent_sequence, IData/*31:0*/ this_priority, CData/*0:0*/ call_pre_post);
  private:
    VlCoroutine __VnoInFunc_start____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &call_pre_post, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> &parent_sequence, VlForkSync __Vfork_1__sync);
  public:
    virtual VlCoroutine __VnoInFunc_start_item(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> item, IData/*31:0*/ set_priority, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base> sequencer);
    void __VnoInFunc_ungrab(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base> sequencer);
    void __VnoInFunc_unlock(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base> sequencer);
    void __VnoInFunc_use_response_handler(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ enable);
    virtual VlCoroutine __VnoInFunc_wait_for_grant(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ item_priority, CData/*0:0*/ lock_request);
    virtual VlCoroutine __VnoInFunc_wait_for_item_done(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ transaction_id);
    virtual VlCoroutine __VnoInFunc_wait_for_relevant(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_wait_for_sequence_state(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ state_mask);
  private:
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base>& obj);

#endif  // guard
