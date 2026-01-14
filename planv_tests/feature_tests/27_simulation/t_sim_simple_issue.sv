// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: simulation behavior for simple issue reproduction

`include "test_utils.svh"

module t_sim_simple_issue;

  // Clock and Reset
  logic clk;
  logic rst_n;

  // Test Inputs
  logic [1:0] issue_instr_ack_i;
  logic [1:0] fetch_entry_valid_i;
  logic flush_i;
  logic [1:0][31:0] decoded_instruction;
  logic [1:0][31:0] orig_instr;
  logic [1:0] is_control_flow_instr;

  // Internal Signals
  typedef struct packed {
    logic valid;
    logic [31:0] sbe;
    logic [31:0] orig_instr;
    logic is_ctrl_flow;
  } issue_entry_t;

  issue_entry_t [1:0] issue_q;
  issue_entry_t [1:0] issue_n;

  // Simulate DUT behavior
  always_comb begin
    issue_n = issue_q;

    // Example combinational logic
    if (fetch_entry_valid_i[0]) begin
      issue_n[0].valid = 1'b1;
      issue_n[0].sbe = decoded_instruction[0];
      issue_n[0].orig_instr = orig_instr[0];
      issue_n[0].is_ctrl_flow = is_control_flow_instr[0];
    end

    if (fetch_entry_valid_i[1]) begin
      issue_n[1].valid = 1'b1;
      issue_n[1].sbe = decoded_instruction[1];
      issue_n[1].orig_instr = orig_instr[1];
      issue_n[1].is_ctrl_flow = is_control_flow_instr[1];
    end

    if (flush_i) begin
      issue_n[0].valid = 1'b0;
      issue_n[1].valid = 1'b0;
    end
  end

  // Simulate sequential behavior
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      issue_q <= '0;
    end else begin
      issue_q <= issue_n;
    end
  end

  // Clock generation
  always #5 clk = ~clk;

  // Test procedure
  initial begin
    // Initialize signals
    clk = 0;
    rst_n = 0;
    fetch_entry_valid_i = 0;
    decoded_instruction = '{32'hDEADBEEF, 32'hFEEDBEEF};
    orig_instr = '{32'hCAFEBABE, 32'hDEADCAFE};
    is_control_flow_instr = 2'b10; // Control flow for port 0 only
    flush_i = 0;

    // Apply reset
    #10 rst_n = 1;

    // Test Case 1: Normal fetch and store for port 0
    fetch_entry_valid_i[0] = 1;
    #10;
    fetch_entry_valid_i[0] = 0;

    // Check if issue_q follows issue_n
    if (issue_q[0].valid !== issue_n[0].valid || issue_q[0].sbe !== decoded_instruction[0]) begin
      `DBG(("Error: issue_q[0] does not follow issue_n[0]"))
      $stop;
    end

    // Test Case 2: Normal fetch and store for port 1
    fetch_entry_valid_i[1] = 1;
    #10;
    fetch_entry_valid_i[1] = 0;

    if (issue_q[1].valid !== issue_n[1].valid || issue_q[1].sbe !== decoded_instruction[1]) begin
      `DBG(("Error: issue_q[1] does not follow issue_n[1]"))
      $stop;
    end

    // Test Case 3: Flush
    flush_i = 1;
    #10 flush_i = 0;

    if (issue_q[0].valid !== 0 || issue_q[1].valid !== 0) begin
      `DBG(("Error: issue_q not cleared after flush"))
      $stop;
    end

    // Test Case 4: Repeated fetch on port 0
    fetch_entry_valid_i[0] = 1;
    decoded_instruction[0] = 32'hABCDEF01; // New instruction
    orig_instr[0] = 32'h10203040;
    #10;

    if (issue_q[0].sbe !== 32'hABCDEF01 || issue_q[0].orig_instr !== 32'h10203040) begin
      `DBG(("Error: issue_q[0] not updated correctly on repeated fetch"))
      $stop;
    end

    // Finish simulation
    `TEST_PASS
  end

endmodule
