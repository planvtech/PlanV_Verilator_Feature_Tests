// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See uvmt_fifo_tb.h for the primary calling header

#ifndef VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SEQUENCER_BASE__VCLPKG_H_
#define VERILATED_UVMT_FIFO_TB_UVM_PKG__03A__03AUVM_SEQUENCER_BASE__VCLPKG_H_  // guard

#include "verilated.h"
#include "verilated_timing.h"
#include "verilated_random.h"
class uvmt_fifo_tb_std__03a__03aprocess;
class uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_37;
class uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_72;
class uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_79;
class uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80;
class uvmt_fifo_tb_uvm_pkg__03a__03am_uvm_sqr_seq_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_component;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_coreservice_t;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_factory;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_object_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_queue__Tz8;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz18;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource__Tz36;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_resource_pool;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_root;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_seed_map;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_process_wrapper;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_request;
class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base;


class uvmt_fifo_tb__Syms;

class alignas(VL_CACHE_LINE_BYTES) uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base__Vclpkg final {
  public:

    // DESIGN SPECIFIC STATE
    IData/*31:0*/ __PVT__g_request_id;
    IData/*31:0*/ __PVT__g_sequence_id;
    IData/*31:0*/ __PVT__g_sequencer_id;
    VlAssocArray<IData/*31:0*/, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base>> __PVT__all_sequencer_insts;

    // INTERNAL VARIABLES
    uvmt_fifo_tb__Syms* vlSymsp;
    const char* vlNamep;

    // CONSTRUCTORS
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base__Vclpkg();
    ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base__Vclpkg();
    void ctor(uvmt_fifo_tb__Syms* symsp, const char* namep);
    void dtor();
    VL_UNCOPYABLE(uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base__Vclpkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};

#include "uvmt_fifo_tb_uvm_pkg__03a__03auvm_component__Vclpkg.h"

class uvmt_fifo_tb__Syms;

class uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base : public uvmt_fifo_tb_uvm_pkg__03a__03auvm_component {
  public:

    // DESIGN SPECIFIC STATE
    CData/*0:0*/ __PVT__m_auto_item_recording;
    CData/*0:0*/ __Vtrigprevexpr_h1c8f93e9__0;
    CData/*0:0*/ __Vtrigprevexpr_h0446bf92__0;
    CData/*0:0*/ __Vtrigprevexpr_hdd466198__0;
    CData/*0:0*/ __Vtrigprevexpr_h001a9213__0;
    CData/*0:0*/ __Vtrigprevexpr_h6c9127cf__0;
    CData/*0:0*/ __Vtrigprevexpr_h67d55879__0;
    CData/*0:0*/ __Vtrigprevexpr_hb767c568__0;
    IData/*31:0*/ __PVT__m_sequencer_id;
    IData/*31:0*/ __PVT__m_lock_arb_size;
    IData/*31:0*/ __PVT__m_arb_size;
    IData/*31:0*/ __PVT__m_wait_for_item_sequence_id;
    IData/*31:0*/ __PVT__m_wait_for_item_transaction_id;
    IData/*31:0*/ __PVT__m_wait_relevant_count;
    IData/*31:0*/ __PVT__m_max_zero_time_wait_relevant_count;
    IData/*31:0*/ __PVT__m_arbitration;
    IData/*31:0*/ __PVT__m_is_relevant_completed;
    QData/*63:0*/ __PVT__m_last_wait_relevant_time;
    VlAssocArray<IData/*31:0*/, CData/*0:0*/> __PVT__arb_completed;
    VlQueue<IData/*31:0*/> __Vtask___VforkTask_2__57__is_relevant_entries;
    VlQueue<IData/*31:0*/> __Vtask___VforkTask_1__58__is_relevant_entries;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_request>> __PVT__arb_sequence_q;
    VlQueue<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base>> __PVT__lock_list;
    VlAssocArray<IData/*31:0*/, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base>> __PVT__reg_sequences;
    VlAssocArray<VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase>, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_process_wrapper>> __PVT__m_default_sequences;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_72> __Vtask___VforkTask_2__57____VDynScope_m_wait_for_available_sequence_0;
    VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> __Vtask___VforkTask_1__58__unnamedblk242__DOT____VforkParent;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_79> __Vtask___VforkTask_1__58__unnamedblk242__DOT___Vwrapped_unnamedblk243_7__DOT____VDynScope_unnamedblk243_7;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_37> __Vtask_uvm_wait_for_nba_region__149____VDynScope_uvm_wait_for_nba_region_0;
    VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_37> __Vtask___VforkTask_0__151____VDynScope_uvm_wait_for_nba_region_0;
    virtual void __VnoInFunc___VBasicRand(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &__VBasicRand__Vfuncrtn);
    virtual void __VnoInFunc___Vsetup_constraints(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_analysis_write(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t);
    void __VnoInFunc_convert2string(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string &convert2string__Vfuncrtn);
    virtual void __VnoInFunc_current_grabber(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> &current_grabber__Vfuncrtn);
    virtual void __VnoInFunc_disable_auto_item_recording(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_do_print(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_printer> printer);
    virtual VlCoroutine __VnoInFunc_execute_item(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> item);
    void __VnoInFunc_get_arbitration(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &get_arbitration__Vfuncrtn);
    virtual void __VnoInFunc_get_arbitration_sequence(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ index, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> &get_arbitration_sequence__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_grab(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr);
    void __VnoInFunc_grant_queued_locks(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_has_do_available(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &has_do_available__Vfuncrtn);
    void __VnoInFunc_has_lock(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr, CData/*0:0*/ &has_lock__Vfuncrtn);
    virtual void __VnoInFunc_is_auto_item_recording_enabled(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_auto_item_recording_enabled__Vfuncrtn);
    void __VnoInFunc_is_blocked(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr, CData/*0:0*/ &is_blocked__Vfuncrtn);
    void __VnoInFunc_is_child(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> parent, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> child, CData/*0:0*/ &is_child__Vfuncrtn);
    virtual void __VnoInFunc_is_grabbed(uvmt_fifo_tb__Syms* __restrict vlSymsp, CData/*0:0*/ &is_grabbed__Vfuncrtn);
    void __VnoInFunc_kill_sequence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr);
    virtual VlCoroutine __VnoInFunc_lock(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr);
    void __VnoInFunc_m_choose_next_request(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &m_choose_next_request__Vfuncrtn);
    virtual void __VnoInFunc_m_find_number_driver_connections(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &m_find_number_driver_connections__Vfuncrtn);
    void __VnoInFunc_m_find_sequence(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ sequence_id, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> &m_find_sequence__Vfuncrtn);
    void __VnoInFunc_m_get_seq_item_priority(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_request> seq_q_entry, IData/*31:0*/ &m_get_seq_item_priority__Vfuncrtn);
    VlCoroutine __VnoInFunc_m_lock_req(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr, CData/*0:0*/ lock);
    virtual void __VnoInFunc_m_register_sequence(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr, IData/*31:0*/ &m_register_sequence__Vfuncrtn);
    VlCoroutine __VnoInFunc_m_select_sequence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    void __VnoInFunc_m_sequence_exiting(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr);
    void __VnoInFunc_m_set_arbitration_completed(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ request_id);
    void __VnoInFunc_m_unlock_req(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr);
    virtual void __VnoInFunc_m_unregister_sequence(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ sequence_id);
    void __VnoInFunc_m_update_lists(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_m_wait_arb_not_equal(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_m_wait_for_arbitration_completed(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ request_id);
    VlCoroutine __VnoInFunc_m_wait_for_available_sequence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    VlCoroutine __VnoInFunc_m_wait_for_available_sequence____Vfork_1__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<IData/*31:0*/> &is_relevant_entries, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_72> &__VDynScope_m_wait_for_available_sequence_0, VlForkSync __Vfork_1__sync);
    VlCoroutine __VnoInFunc_m_wait_for_available_sequence____Vfork_1__0____Vfork_2__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<IData/*31:0*/> is_relevant_entries, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_72> __VDynScope_m_wait_for_available_sequence_0, VlForkSync __Vfork_2__sync);
    VlCoroutine __VnoInFunc_m_wait_for_available_sequence____Vfork_1__0____Vfork_2__0____Vfork_3__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlForkSync __Vfork_3__sync);
    VlCoroutine __VnoInFunc_m_wait_for_available_sequence____Vfork_1__0____Vfork_2__0____Vfork_3__0____Vfork_4__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_m_wait_for_available_sequence____Vfork_1__0____Vfork_2__0____Vfork_3__1(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlForkSync __Vfork_3__sync);
  public:
    virtual void __VnoInFunc_randomize(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ &randomize__Vfuncrtn);
    void __VnoInFunc_remove_sequence_from_queues(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr);
    virtual void __VnoInFunc_send_request(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_item> t, CData/*0:0*/ rerandomize);
    void __VnoInFunc_set_arbitration(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ val);
    virtual void __VnoInFunc_set_max_zero_time_wait_relevant_count(uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ new_val);
    virtual void __VnoInFunc_start_phase_sequence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
  private:
    VlCoroutine __VnoInFunc_start_phase_sequence____Vfork_7__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03a__VDynScope_80> __VDynScope_start_phase_sequence_8, VlClassRef<uvmt_fifo_tb_std__03a__03aprocess> unnamedblk251__DOT____VforkParent);
  public:
    virtual void __VnoInFunc_stop_phase_sequence(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_phase> phase);
    virtual void __VnoInFunc_stop_sequences(uvmt_fifo_tb__Syms* __restrict vlSymsp);
    virtual void __VnoInFunc_ungrab(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr);
    virtual void __VnoInFunc_unlock(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr);
    virtual void __VnoInFunc_user_priority_arbitration(uvmt_fifo_tb__Syms* __restrict vlSymsp, VlQueue<IData/*31:0*/> avail_sequences, IData/*31:0*/ &user_priority_arbitration__Vfuncrtn);
    virtual VlCoroutine __VnoInFunc_wait_for_grant(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr, IData/*31:0*/ item_priority, CData/*0:0*/ lock_request);
    virtual VlCoroutine __VnoInFunc_wait_for_item_done(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequence_base> sequence_ptr, IData/*31:0*/ transaction_id);
    virtual VlCoroutine __VnoInFunc_wait_for_sequences(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
  private:
    VlCoroutine __VnoInFunc_wait_for_sequences____Vfork_5__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp);
    VlCoroutine __VnoInFunc_wait_for_sequences____Vfork_5__0____Vfork_6__0(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, IData/*31:0*/ __Vintraval_hf6e582b1__0);
    void _ctor_var_reset(uvmt_fifo_tb__Syms* __restrict vlSymsp);
  public:
    uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base(VlProcessRef vlProcess, uvmt_fifo_tb__Syms* __restrict vlSymsp, std::string name, VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_component> parent);
    std::string to_string() const;
    std::string to_string_middle() const;
    virtual ~uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base();
};

std::string VL_TO_STRING(const VlClassRef<uvmt_fifo_tb_uvm_pkg__03a__03auvm_sequencer_base>& obj);

#endif  // guard
