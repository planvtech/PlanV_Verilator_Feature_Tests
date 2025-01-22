// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2024. All rights reserved.
// Contact: yilou.wang@planv.tech

module tb_pipeline_register;

  // Clock and Reset
  logic clk;
  logic rst_n;

  // DUT Inputs
  logic [1:0] issue_instr_ack_i;
  logic [1:0] fetch_entry_valid_i;
  logic flush_i;
  logic stall_instr_fetch;
  logic [31:0] decoded_instruction[1:0];
  logic [31:0] orig_instr[1:0];
  logic [0:0] is_control_flow_instr[1:0];

  // DUT Outputs
  logic [1:0] fetch_entry_ready_o;
  logic [1:0] issue_entry_valid_o;
  logic [1:0] is_ctrl_flow_o;
  logic [31:0] orig_instr_o[1:0];

  // Internal Signals
  typedef struct packed {
    logic valid;
    logic [31:0] sbe;
  } issue_entry_t;

  issue_entry_t issue_q[1:0];
  issue_entry_t issue_n[1:0];

  // DUT Instance
  pipeline_register #(
    .NrIssuePorts(2),
    .FpgaAlteraEn(0),
    .SuperscalarEn(1)
  ) dut (
    .clk_i(clk),
    .rst_ni(rst_n),
    .issue_instr_ack_i(issue_instr_ack_i),
    .fetch_entry_valid_i(fetch_entry_valid_i),
    .flush_i(flush_i),
    .stall_instr_fetch(stall_instr_fetch),
    .decoded_instruction(decoded_instruction),
    .orig_instr(orig_instr),
    .is_control_flow_instr(is_control_flow_instr),
    .fetch_entry_ready_o(fetch_entry_ready_o),
    .issue_entry_valid_o(issue_entry_valid_o),
    .is_ctrl_flow_o(is_ctrl_flow_o),
    .orig_instr_o(orig_instr_o)
  );

  // Clock Generation
  always #5 clk = ~clk;

  // Test Procedure
  initial begin
    // Initialize signals
    clk = 0;
    rst_n = 0;
    issue_instr_ack_i = 0;
    fetch_entry_valid_i = 0;
    flush_i = 0;
    stall_instr_fetch = 0;
    decoded_instruction = '{default:32'h0};
    orig_instr = '{default:32'h0};
    is_control_flow_instr = '{default:1'b0};

    // Apply Reset
    #10 rst_n = 1;

    // Test Case 1: Simple instruction fetch
    fetch_entry_valid_i[0] = 1;
    decoded_instruction[0] = 32'hA5A5A5A5;
    orig_instr[0] = 32'h5A5A5A5A;
    is_control_flow_instr[0] = 1;
    #10;

    if (fetch_entry_ready_o[0] != 1) begin
      $stop;
    end
    if (issue_entry_valid_o[0] != 1) begin
      $stop;
    end

    // Test Case 2: Flush condition
    flush_i = 1;
    #10 flush_i = 0;
    if (issue_entry_valid_o[0] != 0) begin
      $stop;
    end

    // Test Case 3: Superscalar issue behavior
    fetch_entry_valid_i = 2'b11;
    decoded_instruction = '{32'hDEADBEEF, 32'hFEEDBEEF};
    orig_instr = '{32'h12345678, 32'h87654321};
    is_control_flow_instr = '{1'b1, 1'b0};
    issue_instr_ack_i[0] = 1;
    #10;

    if (issue_entry_valid_o[1] != 1) begin
      $stop;
    end

    // Finish
    $write("*-* All Finished *-*");
    $finish;
  end
endmodule
