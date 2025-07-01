// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2025. All rights reserved.
// Contact: yilou.wang@planv.tech

module id_stage (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // Fetch flush request - CONTROLLER
    input logic flush_i,
    // Handshake's data between fetch and decode - FRONTEND
    input logic [1:0][31:0] fetch_entry_i,
    // Handshake's valid between fetch and decode - FRONTEND
    input logic [1:0] fetch_entry_valid_i,
    // Handshake's ready between fetch and decode - FRONTEND
    output logic [1:0] fetch_entry_ready_o,
    // Handshake's data between decode and issue - ISSUE
    output logic [1:0][31:0] issue_entry_o,
    output logic [1:0][31:0] issue_entry_o_prev,
    // Instruction value - ISSUE
    output logic [1:0][31:0] orig_instr_o,
    // Handshake's valid between decode and issue - ISSUE
    output logic [1:0] issue_entry_valid_o,
    // Report if instruction is a control flow instruction - ISSUE
    output logic [1:0] is_ctrl_flow_o,
    // Handshake's acknowlege between decode and issue - ISSUE
    input logic [1:0] issue_instr_ack_i
);
  // ID/ISSUE register stage
  typedef struct packed {
    logic       valid;
    logic [31:0] sbe;
    logic [31:0] orig_instr;
    logic       is_ctrl_flow;
  } issue_struct_t;
  issue_struct_t [1:0] issue_n, issue_q;

  always_comb begin
    issue_n             = issue_q;
    fetch_entry_ready_o = '0;

    // Clear the valid flag if issue has acknowledged the instruction
    if (issue_instr_ack_i[0]) issue_n[0].valid = 1'b0;

    // if we have a space in the register and the fetch is valid, go get it
    // or the issue stage is currently acknowledging an instruction, which means that we will have space
    // for a new instruction
    if ((!issue_q[0].valid || issue_instr_ack_i[0]) && fetch_entry_valid_i[0]) begin
      fetch_entry_ready_o[0] = 1'b1;
      issue_n[0] = '{1'b1, fetch_entry_i[0], fetch_entry_i[0], 1'b0};
    end

    // invalidate the pipeline register on a flush
    if (flush_i) issue_n[0].valid = 1'b0;
  end

  // Pipeline Register
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      issue_q <= '0;
    end else begin
      issue_q <= issue_n;
    end
  end

for (genvar i = 0; i < 2; i++) begin
  assign issue_entry_o[i] = issue_q[i].sbe;
  assign issue_entry_o_prev[i] = 1 ? issue_n[i].sbe : '0;
  assign issue_entry_valid_o[i] = issue_q[i].valid;
  assign is_ctrl_flow_o[i] = issue_q[i].is_ctrl_flow;
  assign orig_instr_o[i] = issue_q[i].orig_instr;
end

endmodule

module tb_id_stage();

  // Parameters
  parameter CLK_PERIOD = 10;
  parameter NUM_ENTRIES = 100; // Number of fetch entries for extensive testing

  // Signals
  logic clk;
  logic rst_n;
  logic flush;
  logic [1:0][31:0] fetch_entry;
  logic [1:0] fetch_entry_valid;
  logic [1:0] fetch_entry_ready;
  logic [1:0][31:0] issue_entry;
  logic [1:0][31:0] issue_entry_prev;
  logic [1:0][31:0] orig_instr;
  logic [1:0] issue_entry_valid_out;
  logic [1:0] is_ctrl_flow;
  logic [1:0] issue_instr_ack;

  // Instantiate the id_stage module
  id_stage uut (
    .clk_i(clk),
    .rst_ni(rst_n),
    .flush_i(flush),
    .fetch_entry_i(fetch_entry),
    .fetch_entry_valid_i(fetch_entry_valid),
    .fetch_entry_ready_o(fetch_entry_ready),
    .issue_entry_o(issue_entry),
    .issue_entry_o_prev(issue_entry_prev),
    .orig_instr_o(orig_instr),
    .issue_entry_valid_o(issue_entry_valid_out),
    .is_ctrl_flow_o(is_ctrl_flow),
    .issue_instr_ack_i(issue_instr_ack)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever begin
      #(CLK_PERIOD / 2) clk = ~clk;
    end
  end

  // Reset generation
  initial begin
    rst_n = 0;
    # (4 * CLK_PERIOD);
    rst_n = 1;
  end

  // Stimulus 1 generation
  initial begin
    fetch_entry_valid = '1;
    issue_instr_ack = '1;
    flush = 0;
  end

  // Test procedure
  initial begin
    fetch_entry = '0;
    // #(CLK_PERIOD / 2);
    // Apply test stimulus
    for (int i = 0; i < NUM_ENTRIES; i++) begin
      // Generate random fetch entries
      fetch_entry[0] = $random;
      fetch_entry[1] = $random;

      # (CLK_PERIOD);
    end
    # (CLK_PERIOD * NUM_ENTRIES);
    // Successful execution marker
    $write("*-* All Finished *-*");
    $finish;
  end

  // Self-checks using if-else print statements
  always @(posedge clk) begin
    if (!rst_n) begin
      if (uut.issue_q[0].valid != 0) $display("ERROR: issue_q[0].valid should be 0 after reset");
      else $display("PASS: issue_q[0].valid is 0 after reset");
    end
    if (fetch_entry_valid[0] && !uut.issue_q[0].valid) begin
      if (uut.issue_n[0].valid != 1) $display("ERROR: issue_n[0].valid should be 1 when fetch_entry_valid[0] is asserted and issue_q[0] is not valid");
      else $display("PASS: issue_n[0].valid is 1 when fetch_entry_valid[0] is asserted and issue_q[0] is not valid");
      
      if (uut.issue_n[0].sbe != fetch_entry[0]) $display("ERROR: issue_n[0].sbe should match fetch_entry[0]");
      else $display("PASS: issue_n[0].sbe matches fetch_entry[0]");
    end
    if (issue_instr_ack[0]) begin
      if (uut.issue_n[0].valid != 0) $display("ERROR: issue_n[0].valid should be 0 when issue_instr_ack[0] is asserted");
      else $display("PASS: issue_n[0].valid is 0 when issue_instr_ack[0] is asserted");
    end
    if (flush) begin
      if (uut.issue_n[0].valid != 0) $display("ERROR: issue_n[0].valid should be 0 when flush is asserted");
      else $display("PASS: issue_n[0].valid is 0 when flush is asserted");
    end
  end

  // Dump waveforms
  initial begin
    $dumpfile("tb_id_stage.vcd");
    $dumpvars(0, tb_id_stage);
  end

endmodule
