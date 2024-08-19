class QueueTest;
    rand int size;
    rand int queue_data[$];

    function new();
        size = 5;
    endfunction
endclass

module queue_test;
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