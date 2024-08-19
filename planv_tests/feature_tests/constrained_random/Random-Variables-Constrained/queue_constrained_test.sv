class QueueTest;
    rand int size;
    rand int queue_data[$];

    function new();
        size = 5;
    endfunction

    // Constraint block
    constraint queue_constraints {
        size inside {[1:10]};            // Constrain size to be between 1 and 10
        queue_data.size() == size;       // Constrain the size of the queue to match the size variable
        foreach(queue_data[i]) {
            queue_data[i] inside {[0:100]};  // Constrain each element of the queue_data to be between 0 and 100
        }
    }
endclass

module queue_constrained_test;
    QueueTest queue_test_instance;
    initial begin
        queue_test_instance = new();
        repeat(10) begin
            if (!queue_test_instance.randomize()) $error("Randomization failed");
            $display("size: %0d, queue_data: %p", queue_test_instance.size, queue_test_instance.queue_data);
        end
        $finish;
    end
endmodule