// DESCRIPTION: PlanV Verilator Feature Tests
//
// Property of PlanV GmbH, 2026. All rights reserved.
// Licensed under the Solderpad Hardware License, Version 2.0. See the LICENSE file in the project root for more information.
// Contact: yilou.wang@planv.tech
//
// This test validates: simulation behavior for Ariane regfile FPGA design

`include "test_utils.svh"

module ariane_regfile_fpga #(
    parameter int unsigned           DATA_WIDTH    = 32,
    parameter int unsigned           NR_READ_PORTS = 2,
    parameter int unsigned           NrCommitPorts = 2,
    parameter bit                    ZERO_REG_ZERO = 0
) (
    // clock and reset
    input  logic                                             clk_i,
    input  logic                                             rst_ni,
    // disable clock gates for testing
    input  logic                                             test_en_i,
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
      if (0) raddr_q <= raddr_i;  // FpgaAlteraEn is 0 in this configuration
      else raddr_q <= '0;
    end
  end

  // distributed RAM blocks
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] mem_read[NrCommitPorts];
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] mem_read_sync[NrCommitPorts];
  for (genvar j = 0; j < NrCommitPorts; j++) begin : regfile_ram_block
    // NOTE: Using always @(posedge clk_i) instead of always_ff to allow initial block randomization
    always @(posedge clk_i) begin
      if (we_i[j] && ~waddr_i[j] != 0) begin
        mem[j][waddr_i[j]] <= wdata_i[j];
        if (0)
          wdata_reg[j] <= wdata_i[j];  // FpgaAlteraEn is 0 in this configuration
        else wdata_reg[j] <= '0;
      end
      if (0) begin
        for (int k = 0; k < NR_READ_PORTS; k++) begin : block_read
          mem_read_sync[j][k] = mem[j][raddr_i[k]];  // synchronous RAM
          read_after_write[j][k] <= '0;
          if (waddr_i[j] == raddr_i[k])
            read_after_write[j][k] <= we_i[j] && ~waddr_i[j] != 0; // Identify if we need to read the content that was written
        end
      end
    end
    for (genvar k = 0; k < NR_READ_PORTS; k++) begin : block_read
      assign mem_read[j][k] = 0 ? ( read_after_write[j][k] ? wdata_reg[j]: mem_read_sync[j][k]) : mem[j][raddr_i[k]];  // FpgaAlteraEn is 0 in this configuration
    end
  end
  //with synchronous ram there is the need to adjust which address is used at the output MUX
  assign raddr = 0 ? raddr_q : raddr_i;  // FpgaAlteraEn is 0 in this configuration

  // output MUX
  logic [NR_READ_PORTS-1:0][LOG_NR_WRITE_PORTS-1:0] block_addr;
  for (genvar k = 0; k < NR_READ_PORTS; k++) begin : regfile_read_port
    assign block_addr[k] = mem_block_sel_q[raddr[k]];
    assign rdata_o[k] = (ZERO_REG_ZERO && raddr[k] == '0) ? '0 : mem_read[block_addr[k]][k];
  end

  // random initialization of the memory to suppress assert warnings on Questa.
  initial begin
    for (int i = 0; i < NrCommitPorts; i++) begin
      for (int j = 0; j < NUM_WORDS; j++) begin
        if (!0)  // FpgaAlteraEn is 0 in this configuration
          mem[i][j] = $random();  //quartus does not support this random statement on synthesis
        else mem[i][j] = '0;
      end
    end
  end

endmodule


module t_sim_ariane_regfile();

  // Parameters
  parameter int unsigned DATA_WIDTH = 32;
  parameter int unsigned NR_READ_PORTS = 2;
  parameter bit ZERO_REG_ZERO = 0;
  parameter int unsigned NR_WRITE_PORTS = 2;  // assuming 2 write ports for testing

  // Clock and reset
  logic clk_i;
  logic rst_ni;
  logic test_en_i;

  // Read ports
  logic [NR_READ_PORTS-1:0][4:0] raddr_i;
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] rdata_o;

  // Write ports
  logic [NR_WRITE_PORTS-1:0][4:0] waddr_i;
  logic [NR_WRITE_PORTS-1:0][DATA_WIDTH-1:0] wdata_i;
  logic [NR_WRITE_PORTS-1:0] we_i;

  // Instantiate the DUT
  ariane_regfile_fpga #(
    .DATA_WIDTH(DATA_WIDTH),
    .NR_READ_PORTS(NR_READ_PORTS),
    .NrCommitPorts(NR_WRITE_PORTS),
    .ZERO_REG_ZERO(ZERO_REG_ZERO)
  ) dut (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .test_en_i(test_en_i),
    .raddr_i(raddr_i),
    .rdata_o(rdata_o),
    .waddr_i(waddr_i),
    .wdata_i(wdata_i),
    .we_i(we_i)
  );

  // Clock generation
  always #5 clk_i = ~clk_i;

  // Initial block for stimulus
  initial begin
    // Initialize signals
    clk_i = 0;
    rst_ni = 0;
    test_en_i = 0;
    raddr_i = '0;
    waddr_i = '0;
    wdata_i = '0;
    we_i = '0;

    // Reset the DUT
    #10;
    rst_ni = 1;

    // Test case 1: Write and read back
    #10;
    waddr_i[0] = 5'd1;
    wdata_i[0] = 32'hDEADBEEF;
    we_i[0] = 1'b1;
    #10;
    we_i[0] = 1'b0;

    #10;
    raddr_i[0] = 5'd1;
    #10;
    if (rdata_o[0] != 32'hDEADBEEF) $stop;

    // Test case 2: Write to multiple ports and read back
    #10;
    waddr_i[0] = 5'd2;
    wdata_i[0] = 32'hCAFEBABE;
    we_i[0] = 1'b1;
    waddr_i[1] = 5'd3;
    wdata_i[1] = 32'hBAADF00D;
    we_i[1] = 1'b1;
    #10;
    we_i = '0;

    #10;
    raddr_i[0] = 5'd2;
    raddr_i[1] = 5'd3;
    #10;
    if(rdata_o[0] != 32'hCAFEBABE) $stop;
    if(rdata_o[1] != 32'hBAADF00D) $stop;

    // More test cases can be added here

    `TEST_PASS
  end

endmodule
