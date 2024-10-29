// DESCRIPTION: PlanV Verilator Transition Coverage Test
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

module t_coverage_transition;
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

        // Print the coverage report
        stc.print();  
        $write("*-* All Finished *-*\n");  // End marker
        $finish;
    end
endmodule
