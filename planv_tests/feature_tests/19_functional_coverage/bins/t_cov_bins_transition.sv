// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: transition coverage for state changes

`include "test_utils.svh"

module t_cov_bins_transition;
    typedef enum {IDLE, START, RUN, STOP} state_t;
    state_t current_state, next_state;

    // Coverage group to capture transitions between states
    covergroup state_transition_coverage;
        coverpoint current_state;
        coverpoint next_state;
        state_transition: coverpoint current_state {
            bins state_trans = (IDLE => START => RUN => STOP);
        }
    endgroup

    state_transition_coverage stc = new();

    initial begin
        // Initialize state
        current_state = IDLE;
        next_state = START;
        stc.sample();  // Sample coverage

        current_state = START;
        next_state = RUN;
        stc.sample();  // Sample coverage

        current_state = RUN;
        next_state = STOP;
        stc.sample();  // Sample coverage

        // NOTE: covergroup.print() is not defined in IEEE 1800 standard
        `DBG(("Coverage collected: %0.2f%%", $get_coverage()))
        `TEST_PASS  // End marker
    end
endmodule
