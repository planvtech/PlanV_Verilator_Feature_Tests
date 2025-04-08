// DESCRIPTION: PlanV Async Fifo SV UVM Testbench
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech


`ifndef __UVMT_FIFO_TB_SV__
`define __UVMT_FIFO_TB_SV__


module uvmt_fifo_tb;

    import uvm_pkg::*;
    import uvmt_fifo_pkg::*;
    import uvme_fifo_pkg::*;

    // Testbench parameters
    // DUT parameters
    // Env parameters

    // TB Interfaces
    uvmt_fifo_clk_gen_if wr_clk_gen_if();
    uvmt_fifo_clk_gen_if rd_clk_gen_if();

    // Agent Interfaces
    uvma_wr_if write_if(wr_clk_gen_if.clk, wr_clk_gen_if.reset_n);
    uvma_rd_if read_if(rd_clk_gen_if.clk, rd_clk_gen_if.reset_n);

    // DUT Interfaces


    // DUT Instances
    simple_demo_tb simple_demo_tb(
        .w_clk(wr_clk_gen_if.clk),
        .w_rst(wr_clk_gen_if.reset_n),
        .w_data(write_if.data),
        .w_en(write_if.en),
        .w_full(write_if.full), // output

        .r_clk(rd_clk_gen_if.clk),
        .r_rst(rd_clk_gen_if.reset_n),
        .r_data(read_if.data), // output
        .r_empty(read_if.empty), // output
        .r_en(read_if.en)
    );


    // Clock Generation
    initial begin : clock_init_and_activate

        // Specify time format for simulation (units_number, precision_number, suffix_string, minimum_field_width)
        $timeformat(-9, 1, " ns", 6);

        wr_clk_gen_if.set_clk_period(5000);
        wr_clk_gen_if.start_clk_gen();

        rd_clk_gen_if.set_clk_period(7000);
        rd_clk_gen_if.start_clk_gen();

    end : clock_init_and_activate


    // Testbench Entry Point
    initial begin : tb_entry_point

        // Add Interfaces handles to uvm_config_db
        uvm_config_db#(virtual uvmt_fifo_clk_gen_if)::set(.cntxt(null), .inst_name("*"), .field_name("wr_clk_gen_vif"), .value(wr_clk_gen_if));
        uvm_config_db#(virtual uvmt_fifo_clk_gen_if)::set(.cntxt(null), .inst_name("*"), .field_name("rd_clk_gen_vif"), .value(rd_clk_gen_if));
        uvm_config_db#(virtual uvma_wr_if)::set(.cntxt(null), .inst_name("*.env*"), .field_name("wr_vif"), .value(write_if));
        uvm_config_db#(virtual uvma_rd_if)::set(.cntxt(null), .inst_name("*.env*"), .field_name("rd_vif"), .value(read_if));

        // Make DUT ouputs to be visible in the testbench

        // DUT and Env parameters

        // Run Test
        $dumpfile("waveform.vcd");
        $dumpvars(0, uvmt_fifo_tb);
        run_test();

    end : tb_entry_point


    // End-of-test summary point

    final begin : tb_end_of_test
    
        uvm_report_server rs;
        int err_count;
        int warning_count;
        int fatal_count;
        static bit sim_finished = 0;

        rs = uvm_report_server::get_server();
        err_count = rs.get_severity_count(UVM_ERROR);
        warning_count = rs.get_severity_count(UVM_WARNING);
        fatal_count = rs.get_severity_count(UVM_FATAL);

        void'(uvm_config_db#(bit)::get(null, "", "sim_finished", sim_finished));

        $display("\n%m: *** Test Summary ***\n");

        if (sim_finished && (err_count == 0) && (fatal_count == 0)) begin
            $display("    PPPPPPP    AAAAAA    SSSSSS    SSSSSS   EEEEEEEE  DDDDDDD     ");
            $display("    PP    PP  AA    AA  SS    SS  SS    SS  EE        DD    DD    ");
            $display("    PP    PP  AA    AA  SS        SS        EE        DD    DD    ");
            $display("    PPPPPPP   AAAAAAAA   SSSSSS    SSSSSS   EEEEE     DD    DD    ");
            $display("    PP        AA    AA        SS        SS  EE        DD    DD    ");
            $display("    PP        AA    AA  SS    SS  SS    SS  EE        DD    DD    ");
            $display("    PP        AA    AA   SSSSSS    SSSSSS   EEEEEEEE  DDDDDDD     ");
            $display("    ----------------------------------------------------------");
            if (warning_count == 0) begin
            $display("                        SIMULATION PASSED                     ");
            end
            else begin
            $display("                 SIMULATION PASSED with WARNINGS              ");
            end
            $display("    ----------------------------------------------------------");
        end
        else begin
            $display("    FFFFFFFF   AAAAAA   IIIIII  LL        EEEEEEEE  DDDDDDD       ");
            $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
            $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
            $display("    FFFFF     AAAAAAAA    II    LL        EEEEE     DD    DD      ");
            $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
            $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
            $display("    FF        AA    AA  IIIIII  LLLLLLLL  EEEEEEEE  DDDDDDD       ");

            if (sim_finished == 0) begin
                $display("    --------------------------------------------------------");
                $display("                   SIMULATION FAILED - ABORTED              ");
                $display("    --------------------------------------------------------");
            end
            else begin
                $display("    --------------------------------------------------------");
                $display("                       SIMULATION FAILED                    ");
                $display("    --------------------------------------------------------");
            end
        end

    end : tb_end_of_test


endmodule : uvmt_fifo_tb


`endif // __UVMT_FIFO_TB_SV__
