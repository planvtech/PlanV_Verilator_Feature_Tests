// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: simulation behavior for CVA6 FPGA design

`include "test_utils.svh"

module async_reg #(
    parameter int unsigned           NR_READ_PORTS = 2,
    parameter int unsigned           NrCommitPorts = 2,
    parameter int unsigned           DATA_WIDTH    = 32,
    parameter bit                    ZERO_REG_ZERO = 0
) (
    // clock and reset
    input  logic                                             clk_i,
    input  logic                                             rst_ni,
    // read port
    input  logic [        NR_READ_PORTS-1:0][           4:0] raddr_i,
    output logic [        NR_READ_PORTS-1:0][DATA_WIDTH-1:0] rdata_o,
    // write port
    input  logic [NrCommitPorts-1:0][           4:0] waddr_i,
    input  logic [NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata_i,
    input  logic [NrCommitPorts-1:0]                 we_i
);

  localparam ADDR_WIDTH = 5;
  localparam NUM_WORDS = 2 ** ADDR_WIDTH;

  logic [            NUM_WORDS-1:0][DATA_WIDTH-1:0] mem;
  logic [NrCommitPorts-1:0][ NUM_WORDS-1:0] we_dec;


  always_comb begin : we_decoder
    for (int unsigned j = 0; j < NrCommitPorts; j++) begin
      for (int unsigned i = 0; i < NUM_WORDS; i++) begin
        if (waddr_i[j] == i) we_dec[j][i] = we_i[j];
        else we_dec[j][i] = 1'b0;
      end
    end
  end

  // loop from 1 to NUM_WORDS-1 as R0 is nil
  always_ff @(posedge clk_i, negedge rst_ni) begin : register_write_behavioral
    if (~rst_ni) begin
      mem <= '{default: '0};
    end else begin
      for (int unsigned j = 0; j < NrCommitPorts; j++) begin
        for (int unsigned i = 0; i < NUM_WORDS; i++) begin
          if (we_dec[j][i]) begin
            mem[i] <= wdata_i[j];
          end
        end
        if (ZERO_REG_ZERO) begin
          mem[0] <= '0;
        end
      end
    end
  end

  for (genvar i = 0; i < NR_READ_PORTS; i++) begin
    assign rdata_o[i] = mem[raddr_i[i]];
  end

endmodule

// ######################################################
// #                   FPGA REGFILE                     #
// ######################################################

module ariane_regfile_fpga #(
    parameter int unsigned           DATA_WIDTH    = 32,
    parameter int unsigned           NR_READ_PORTS = 2,
    parameter int unsigned           NrCommitPorts = 2,
    parameter bit                    ZERO_REG_ZERO = 0
) (
    // clock and reset
    input  logic                                             clk_i,
    input  logic                                             rst_ni,
    // read port
    input  logic [        NR_READ_PORTS-1:0][           4:0] raddr_i,
    output logic [        NR_READ_PORTS-1:0][DATA_WIDTH-1:0] rdata_o,
    // write port
    input  logic [NrCommitPorts-1:0][           4:0] waddr_i,
    input  logic [NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata_i,
    input  logic [NrCommitPorts-1:0]                 we_i
);

  localparam ADDR_WIDTH = 5;
  localparam NUM_WORDS = 2 ** ADDR_WIDTH;
  localparam LOG_NR_WRITE_PORTS = NrCommitPorts == 1 ? 1 : $clog2(NrCommitPorts);
  localparam FpgaAlteraEn = 1;

  // Distributed RAM usually supports one write port per block - duplicate for each write port.
  logic [NUM_WORDS-1:0][DATA_WIDTH-1:0] mem[NrCommitPorts];

  logic [NrCommitPorts-1:0][NUM_WORDS-1:0] we_dec;
  logic [NUM_WORDS-1:0][LOG_NR_WRITE_PORTS-1:0] mem_block_sel;
  logic [NUM_WORDS-1:0][LOG_NR_WRITE_PORTS-1:0] mem_block_sel_q;
  logic [NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata_reg;
  logic [NR_READ_PORTS-1:0] read_after_write[NrCommitPorts];

  logic [NR_READ_PORTS-1:0][4:0] raddr_q;
  logic [NR_READ_PORTS-1:0][4:0] raddr;

  // write adress decoder (for block selector)
  always_comb begin
    for (int unsigned j = 0; j < NrCommitPorts; j++) begin
      for (int unsigned i = 0; i < NUM_WORDS; i++) begin
        if (waddr_i[j] == i) begin
          we_dec[j][i] = we_i[j];
        end else begin
          we_dec[j][i] = 1'b0;
        end
      end
    end
  end

  // update block selector:
  // signal mem_block_sel records where the current valid value is stored.
  // if multiple ports try to write to the same address simultaneously, the port with the highest
  // index has priority.
  always_comb begin
    mem_block_sel = mem_block_sel_q;
    for (int i = 0; i < NUM_WORDS; i++) begin
      for (int j = 0; j < NrCommitPorts; j++) begin
        if (we_dec[j][i] == 1'b1) begin
          mem_block_sel[i] = LOG_NR_WRITE_PORTS'(j);
        end
      end
    end
  end

  // block selector flops
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mem_block_sel_q <= '0;
      raddr_q <= '0;
    end else begin
      mem_block_sel_q <= mem_block_sel;
      if (FpgaAlteraEn) raddr_q <= raddr_i;
      else raddr_q <= '0;
    end
  end

  // distributed RAM blocks
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] mem_read[NrCommitPorts];
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] mem_read_sync[NrCommitPorts];
  for (genvar j = 0; j < NrCommitPorts; j++) begin : regfile_ram_block
    always_ff @(posedge clk_i) begin
      if (we_i[j] && ~waddr_i[j] != 0) begin
        mem[j][waddr_i[j]] <= wdata_i[j];
        if (FpgaAlteraEn)
          wdata_reg[j] <= wdata_i[j];
        else wdata_reg[j] <= '0;
      end
      if (FpgaAlteraEn) begin
        for (int k = 0; k < NR_READ_PORTS; k++) begin : block_read
          mem_read_sync[j][k] = mem[j][raddr_i[k]];  // synchronous RAM
          read_after_write[j][k] <= '0;
          if (waddr_i[j] == raddr_i[k])
            read_after_write[j][k] <= we_i[j] && ~waddr_i[j] != 0; // Identify if we need to read the content that was written
        end
      end
    end
    for (genvar k = 0; k < NR_READ_PORTS; k++) begin : block_read
      assign mem_read[j][k] = FpgaAlteraEn ? ( read_after_write[j][k] ? wdata_reg[j]: mem_read_sync[j][k]) : mem[j][raddr_i[k]];
    end
  end
  //with synchronous ram there is the need to adjust which address is used at the output MUX
  assign raddr = FpgaAlteraEn ? raddr_q : raddr_i;

  // output MUX
  logic [NR_READ_PORTS-1:0][LOG_NR_WRITE_PORTS-1:0] block_addr;
  for (genvar k = 0; k < NR_READ_PORTS; k++) begin : regfile_read_port
    assign block_addr[k] = mem_block_sel_q[raddr[k]];
    assign rdata_o[k] = (ZERO_REG_ZERO && raddr[k] == '0) ? '0 : mem_read[block_addr[k]][k];
  end

  // random initialization of the memory to suppress assert warnings on Questa.
  /*
  initial begin
    for (int i = 0; i < NrCommitPorts; i++) begin
      for (int j = 0; j < NUM_WORDS; j++) begin
        // if (!FpgaAlteraEn)
        //   mem[i][j] = $random();  //quartus does not support this random statement on synthesis
        mem[i][j] = '0;
      end
    end
  end
  */
endmodule

// ######################################################
// #                  ID STAGE                          #
// ######################################################

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
    output logic [1:0][4:0] issue_entry_o,
    output logic [1:0][4:0] issue_entry_o_prev,
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
    logic [4:0] sbe;
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
  assign issue_entry_o_prev[i] = issue_n[i].sbe;
  assign issue_entry_valid_o[i] = issue_q[i].valid;
  assign is_ctrl_flow_o[i] = issue_q[i].is_ctrl_flow;
  assign orig_instr_o[i] = issue_q[i].orig_instr;
end

endmodule

// ######################################################
// #                  TOP TB                            #
// ######################################################

module t_sim_cva6_fpga();

  // Parameters
  parameter int CLK_PERIOD = 10;
  parameter int NUM_ENTRIES = 1000; // Number of fetch entries for extensive testing
  parameter int unsigned DATA_WIDTH = 32;
  parameter int unsigned NR_READ_PORTS = 2;
  parameter int unsigned NrCommitPorts = 2;

  // Signals
  logic clk;
  logic rst_n;
  logic flush;
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] fetch_entry;
  logic [NR_READ_PORTS-1:0] fetch_entry_valid;
  logic [NR_READ_PORTS-1:0] fetch_entry_ready;
  logic [NR_READ_PORTS-1:0][4:0] issue_entry;
  logic [NR_READ_PORTS-1:0][4:0] issue_entry_prev;
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] orig_instr;
  logic [NR_READ_PORTS-1:0] issue_entry_valid_out;
  logic [NR_READ_PORTS-1:0] is_ctrl_flow;
  logic [NR_READ_PORTS-1:0] issue_instr_ack;
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] async_reg_out;
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] fpga_reg_out;
  logic [NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata;
  logic [NrCommitPorts-1:0][4:0] waddr;
  logic [NrCommitPorts-1:0] we;

  logic flag;
  assign flag = fpga_reg_out == async_reg_out;

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

  // Instantiate the asynchronous register
  async_reg #(
    .DATA_WIDTH(DATA_WIDTH),
    .NR_READ_PORTS(NR_READ_PORTS),
    .NrCommitPorts(NrCommitPorts)
  ) async_reg_inst (
    .clk_i(clk),
    .rst_ni(rst_n),
    .raddr_i(issue_entry),
    .rdata_o(async_reg_out),
    .waddr_i(waddr),
    .wdata_i(wdata),
    .we_i(we)
  );

  // Instantiate the FPGA register
  ariane_regfile_fpga #(
    .DATA_WIDTH(DATA_WIDTH),
    .NR_READ_PORTS(NR_READ_PORTS),
    .NrCommitPorts(NrCommitPorts)
  ) fpga_reg_inst (
    .clk_i(clk),
    .rst_ni(rst_n),
    .raddr_i(issue_entry_prev),
    .rdata_o(fpga_reg_out),
    .waddr_i(waddr),
    .wdata_i(wdata),
    .we_i(we)
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
    wdata = '0;
    waddr = '0;
    we = '0;

    // Reset
    # (2 * CLK_PERIOD);
    rst_n = 1;
    // Generate random write data and addresses
    for (int i = 0; i < 30; i++) begin  
      wdata[0] = $random;
      wdata[1] = $random;
      waddr[0] = $random;
      waddr[1] = $random;
      we[0] = 1;
      we[1] = 1;
      # (CLK_PERIOD);
      we[0] = 0;
      we[1] = 0;
      # (CLK_PERIOD);
    end

    // Apply test stimulus
    for (int i = 0; i < NUM_ENTRIES; i++) begin
      // Generate random fetch entries
      fetch_entry[0] = $random;
      fetch_entry[1] = $random;
      fetch_entry_valid[0] = 1;
      fetch_entry_valid[1] = 1;

      wdata[0] = $random;
      wdata[1] = $random;
      waddr[0] = $random;
      waddr[1] = $random;
      we[0] = 1;
      we[1] = 1;

      # (CLK_PERIOD);
      fetch_entry_valid[0] = 0;
      fetch_entry_valid[1] = 0;
      we[0] = 0;
      we[1] = 0;

      // Issue acknowledgment
      issue_instr_ack[0] = 1;
      issue_instr_ack[1] = 1;

      # (CLK_PERIOD);
      issue_instr_ack[0] = 0;
      issue_instr_ack[1] = 0;

      // Apply flush randomly
      if ($random % 61 == 0) begin
        flush = 1;
        # (CLK_PERIOD);
        flush = 0;
      end

      # (CLK_PERIOD);
    end
    # (CLK_PERIOD * 100);

    // Successful execution marker
    `TEST_PASS
  end

  // Self-checks using if-else print statements
  always @(posedge clk) begin
    // Compare outputs
    for (int i = 0; i < NR_READ_PORTS; i++) begin
      if (async_reg_out[i] !== fpga_reg_out[i]) begin
        `DBG(("ERROR: Async register output and FPGA register output do not match for port %0d", i))
      end
    end
  end

  // Dump waveforms
  initial begin
    $dumpfile("tb_cva6_fpga.vcd");
    $dumpvars(0, tb_cva6_fpga, uut, async_reg_inst, fpga_reg_inst);
  end

endmodule
