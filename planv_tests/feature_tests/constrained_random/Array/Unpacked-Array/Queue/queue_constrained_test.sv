class constrained_queue;

rand int m_intQueue[$];

rand int m_idx;

function new;

m_intQueue = '{6{0}};

endfunction

constraint int_queue_c {

m_idx inside {[0:5]};

m_intQueue[m_idx] == m_idx + 1;

foreach (m_intQueue[i]) {

m_intQueue[i] inside {[0:127]};

}

}

endclass

module queue_constrained_test;

constrained_queue my_queue;

initial begin

my_queue = new();

// Randomization of the unpacked array without constraints

if (!my_queue.randomize()) begin

$display("Unpacked array randomization failed.");

$stop;

end


$display("Queue values (m_intQueue):");
        foreach (my_queue.m_intQueue[i]) begin
            $display("m_intQueue[%0d] = %0d", i, my_queue.m_intQueue[i]);
        end
        $display("Index value: %0d", my_queue.m_idx);

$finish;

end

endmodule