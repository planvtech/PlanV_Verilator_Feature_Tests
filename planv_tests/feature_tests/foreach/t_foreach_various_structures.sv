// DESCRIPTION: PlanV Verilator Foreach Test for Various Queue and Array Structures
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

module t_foreach_various_structures;

    // Define various structures to test foreach behavior
    int queue_unp[$][3];      // Outer dynamic queue with fixed-size inner arrays
    int unp_queue[3][$];      // Fixed-size outer array with dynamic inner queues
    int dyn_queue[][];        // Fully dynamic 2D array
    int queue_dyn[$][];       // Outer dynamic queue with dynamic inner queues
    int dyn_unp[][3];         // Dynamic outer array with fixed-size inner arrays
    int unp_dyn[3][];         // Fixed-size outer array with dynamic inner arrays

    int count_queue_unp, exp_count_queue_unp;
    int count_unp_queue, exp_count_unp_queue;
    int count_dyn_queue, exp_count_dyn_queue;
    int count_queue_dyn, exp_count_queue_dyn;
    int count_dyn_unp, exp_count_dyn_unp;
    int count_unp_dyn, exp_count_unp_dyn;

    initial begin
        // Initialize arrays and queues with sample values
        queue_unp = '{'{1, 2, 3}, '{4, 5, 6}, '{7, 8, 9}};
        unp_queue[0] = '{10, 11};
        unp_queue[1] = '{12, 13, 14};
        unp_queue[2] = '{15};
        dyn_queue = '{'{16, 17}, '{18, 19, 20}};
        queue_dyn = '{'{21, 22}, '{23, 24, 25}};
        dyn_unp = '{'{26, 27, 28}, '{29, 30, 31}};
        unp_dyn[0] = '{32, 33};
        unp_dyn[1] = '{34, 35, 36};
        unp_dyn[2] = '{37};

        // Counting elements in `queue_unp` using foreach
        count_queue_unp = 0;
        foreach (queue_unp[i, j]) count_queue_unp++;
        exp_count_queue_unp = 0;
        foreach (queue_unp[i]) foreach (queue_unp[i][j]) exp_count_queue_unp++;

        // Counting elements in `unp_queue` using foreach
        count_unp_queue = 0;
        foreach (unp_queue[i, j]) count_unp_queue++;
        exp_count_unp_queue = 0;
        foreach (unp_queue[i]) foreach (unp_queue[i][j]) exp_count_unp_queue++;

        // Counting elements in `dyn_queue` using foreach
        count_dyn_queue = 0;
        foreach (dyn_queue[i, j]) count_dyn_queue++;
        exp_count_dyn_queue = 0;
        foreach (dyn_queue[i]) foreach (dyn_queue[i][j]) exp_count_dyn_queue++;

        // Counting elements in `queue_dyn` using foreach
        count_queue_dyn = 0;
        foreach (queue_dyn[i, j]) count_queue_dyn++;
        exp_count_queue_dyn = 0;
        foreach (queue_dyn[i]) foreach (queue_dyn[i][j]) exp_count_queue_dyn++;

        // Counting elements in `dyn_unp` using foreach
        count_dyn_unp = 0;
        foreach (dyn_unp[i, j]) count_dyn_unp++;
        exp_count_dyn_unp = 0;
        foreach (dyn_unp[i]) foreach (dyn_unp[i][j]) exp_count_dyn_unp++;

        // Counting elements in `unp_dyn` using foreach
        count_unp_dyn = 0;
        foreach (unp_dyn[i, j]) count_unp_dyn++;
        exp_count_unp_dyn = 0;
        foreach (unp_dyn[i]) foreach (unp_dyn[i][j]) exp_count_unp_dyn++;

        // Verification checks
        if (count_queue_unp != exp_count_queue_unp) begin
            $display("Error: queue_unp foreach count = %0d, expected = %0d", count_queue_unp, exp_count_queue_unp);
            $stop;
        end

        if (count_unp_queue != exp_count_unp_queue) begin
            $display("Error: unp_queue foreach count = %0d, expected = %0d", count_unp_queue, exp_count_unp_queue);
            $stop;
        end

        if (count_dyn_queue != exp_count_dyn_queue) begin
            $display("Error: dyn_queue foreach count = %0d, expected = %0d", count_dyn_queue, exp_count_dyn_queue);
            $stop;
        end

        if (count_queue_dyn != exp_count_queue_dyn) begin
            $display("Error: queue_dyn foreach count = %0d, expected = %0d", count_queue_dyn, exp_count_queue_dyn);
            $stop;
        end

        if (count_dyn_unp != exp_count_dyn_unp) begin
            $display("Error: dyn_unp foreach count = %0d, expected = %0d", count_dyn_unp, exp_count_dyn_unp);
            $stop;
        end

        if (count_unp_dyn != exp_count_unp_dyn) begin
            $display("Error: unp_dyn foreach count = %0d, expected = %0d", count_unp_dyn, exp_count_unp_dyn);
            $stop;
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
