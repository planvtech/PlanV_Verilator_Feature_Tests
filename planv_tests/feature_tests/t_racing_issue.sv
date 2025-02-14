// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Contact: yilou.wang@planv.tech

module dut (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        in_valid,
    input  logic [31:0] in_data,
    output logic [31:0] out_data,
    output logic [31:0] out_data_prev,
    output logic        out_valid
);

  logic [31:0] data_n, data_q;

  always_comb begin
    data_n = data_q;
    out_valid = 0;
    if (in_valid) begin
      data_n = in_data;
      out_valid = 1;
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      data_q <= '0;
    end else begin
      data_q <= data_n;
    end
  end

  assign out_data = data_q;
  assign out_data_prev = data_n;
endmodule

module t_racing_issue;

  parameter CLK_PERIOD = 10;
  parameter NUM_ENTRIES = 10; // Number of test entries

  logic clk, rst_n;
  logic in_valid, out_valid;
  logic [31:0] in_data;
  logic [31:0] out_data, out_data_prev;
  logic [31:0] expected_data, prev_out_data;

  dut uut (
    .clk(clk),
    .rst_n(rst_n),
    .in_valid(in_valid),
    .in_data(in_data),
    .out_valid(out_valid),
    .out_data(out_data),
    .out_data_prev(out_data_prev)
  );

  always # (CLK_PERIOD / 2) clk = ~clk;

  initial begin
    clk = 0;
    rst_n = 0;
    in_valid = 0;
    in_data = 0;

    #(CLK_PERIOD * 2);
    rst_n = 1;

    fork
      begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
          @(posedge clk);
          in_data = $urandom();
          in_valid = 1;
          @(posedge clk);
          in_valid = 0;
        end
        #(CLK_PERIOD * 2);
      end

      begin
        @(posedge rst_n);
        prev_out_data = '0;

        forever begin
          @(posedge clk);
          if (out_valid) begin
            assert (out_data_prev == prev_out_data)
              else $error("Cycle Mismatch: out_data_prev=%h, next out_data=%h", out_data_prev, prev_out_data);

            assert (out_data == expected_data)
              else $error("Data Mismatch: out_data=%h, expected=%h", out_data, expected_data);
          end

          prev_out_data = out_data_prev;
          expected_data = in_valid ? in_data : expected_data;
        end
      end
    join_any

    $display("*-* All Tests Passed *-*");
    $finish;
  end

  // Dump waveforms
  initial begin
    $dumpfile("t_racing_issue.vcd");
    $dumpvars(0, t_racing_issue);
  end

endmodule
