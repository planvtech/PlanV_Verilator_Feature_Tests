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

  assign issue_entry_o = issue_q.sbe;
  assign issue_entry_o_prev = issue_n.sbe;
  assign issue_entry_valid_o = issue_q.valid;
  assign is_ctrl_flow_o = issue_q.is_ctrl_flow;
  assign orig_instr_o = issue_q.orig_instr;

endmodule

module tb_id_stage();

  // Parameters
  parameter CLK_PERIOD = 10;

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
  always # (CLK_PERIOD / 2) clk = ~clk;

  // Test procedure
  initial begin
    // Initialize signals
    clk = 0;
    rst_n = 0;
    flush = 0;
    fetch_entry = '0;
    fetch_entry_valid = '0;
    issue_instr_ack = '0;

    // Reset
    # (2 * CLK_PERIOD);
    rst_n = 1;

    // Apply test stimulus
    # (2 * CLK_PERIOD);
    fetch_entry[0] = 32'hDEADBEEF;
    fetch_entry_valid[0] = 1;
    issue_instr_ack[0] = 0;

    # (2 * CLK_PERIOD);
    fetch_entry_valid[0] = 0;
    issue_instr_ack[0] = 1;

    # (2 * CLK_PERIOD);
    issue_instr_ack[0] = 0;

    // Apply flush
    # (2 * CLK_PERIOD);
    flush = 1;

    # (2 * CLK_PERIOD);
    flush = 0;

    # (2 * CLK_PERIOD);
    // Successful execution marker
    $write("*-* All Finished *-*");
    $finish;
  end

  // Self-checks using assertions
  always @(posedge clk) begin
    if (!rst_n) begin
      if(issue_q[0].valid != 0) $stop;
    end
    if (fetch_entry_valid[0] && !issue_q[0].valid) begin
      if(issue_n[0].valid != 1) $stop;
      if(issue_n[0].sbe != fetch_entry[0]) $stop;
    end
    if (issue_instr_ack[0]) begin
      if(issue_n[0].valid != 0) $stop;
    end
    if (flush) begin
      if(issue_n[0].valid != 0) $stop;
    end
  end

endmodule
