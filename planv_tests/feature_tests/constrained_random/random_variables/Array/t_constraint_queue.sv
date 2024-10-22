// DESCRIPTION: PlanV Verilator Constrained Randomization Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

class ConstrainedQueue;
    rand int m_intQueue[$];
    rand int m_idx;

    // Constructor
    function new();
        m_intQueue = '{6{0}}; // Initialize queue with zeros
    endfunction

    // Constraints for queue
    constraint int_queue_c {
        m_idx inside {[0:5]};  // Index must be within the range of the queue
        m_intQueue[m_idx] == m_idx + 1;  // Constraint on the value at m_idx
        foreach (m_intQueue[i]) {
            m_intQueue[i] inside {[0:127]}; // Values in the queue must be between 0 and 127
        }
    }

    // Self-check function to validate constraints
    function void check();
        if (!(m_idx inside {[0:5]})) begin
            $display("Error: m_idx = %0d is out of bounds", m_idx);
            $stop;
        end
        
        if (m_intQueue[m_idx] != m_idx + 1) begin
            $display("Error: m_intQueue[%0d] = %0d does not equal %0d", m_idx, m_intQueue[m_idx], m_idx + 1);
            $stop;
        end
        
        foreach (m_intQueue[i]) begin
            if (!(m_intQueue[i] inside {[0:127]})) begin
                $display("Error: m_intQueue[%0d] = %0d is out of bounds", i, m_intQueue[i]);
                $stop;
            end
        end
        
        $display("All constraints validated successfully.");
    endfunction
endclass

module t_constraint_queue;
    ConstrainedQueue my_queue;

    initial begin
        my_queue = new();

        // Randomization of the constrained queue
        if (!my_queue.randomize()) begin
            $display("Constrained queue randomization failed.");
            $stop;
        end

        // Self-check to validate constraints after randomization
        my_queue.check();

        // Displaying the values after randomization
        $display("Queue values (m_intQueue):");
        foreach (my_queue.m_intQueue[i]) begin
            $display("m_intQueue[%0d] = %0d", i, my_queue.m_intQueue[i]);
        end
        $display("Index value: %0d", my_queue.m_idx);

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
