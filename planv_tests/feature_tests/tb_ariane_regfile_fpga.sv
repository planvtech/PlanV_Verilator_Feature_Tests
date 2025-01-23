
module ariane_regfile_fpga #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg       = config_pkg::cva6_cfg_empty,
    parameter int unsigned           DATA_WIDTH    = 32,
    parameter int unsigned           NR_READ_PORTS = 2,
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
    input  logic [CVA6Cfg.NrCommitPorts-1:0][           4:0] waddr_i,
    input  logic [CVA6Cfg.NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata_i,
    input  logic [CVA6Cfg.NrCommitPorts-1:0]                 we_i
);

  localparam ADDR_WIDTH = 5;
  localparam NUM_WORDS = 2 ** ADDR_WIDTH;
  localparam LOG_NR_WRITE_PORTS = CVA6Cfg.NrCommitPorts == 1 ? 1 : $clog2(CVA6Cfg.NrCommitPorts);

  // Distributed RAM usually supports one write port per block - duplicate for each write port.
  logic [NUM_WORDS-1:0][DATA_WIDTH-1:0] mem[CVA6Cfg.NrCommitPorts];

  logic [CVA6Cfg.NrCommitPorts-1:0][NUM_WORDS-1:0] we_dec;
  logic [NUM_WORDS-1:0][LOG_NR_WRITE_PORTS-1:0] mem_block_sel;
  logic [NUM_WORDS-1:0][LOG_NR_WRITE_PORTS-1:0] mem_block_sel_q;
  logic [CVA6Cfg.NrCommitPorts-1:0][DATA_WIDTH-1:0] wdata_reg;
  logic [NR_READ_PORTS-1:0] read_after_write[CVA6Cfg.NrCommitPorts];

  logic [NR_READ_PORTS-1:0][4:0] raddr_q;
  logic [NR_READ_PORTS-1:0][4:0] raddr;

  // write adress decoder (for block selector)
  always_comb begin
    for (int unsigned j = 0; j < CVA6Cfg.NrCommitPorts; j++) begin
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
      for (int j = 0; j < CVA6Cfg.NrCommitPorts; j++) begin
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
      if (CVA6Cfg.FpgaAlteraEn) raddr_q <= raddr_i;
      else raddr_q <= '0;
    end
  end

  // distributed RAM blocks
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] mem_read[CVA6Cfg.NrCommitPorts];
  logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0] mem_read_sync[CVA6Cfg.NrCommitPorts];
  for (genvar j = 0; j < CVA6Cfg.NrCommitPorts; j++) begin : regfile_ram_block
    always_ff @(posedge clk_i) begin
      if (we_i[j] && ~waddr_i[j] != 0) begin
        mem[j][waddr_i[j]] <= wdata_i[j];
        if (CVA6Cfg.FpgaAlteraEn)
          wdata_reg[j] <= wdata_i[j];  // register data written in case is needed to read next cycle
        else wdata_reg[j] <= '0;
      end
      if (CVA6Cfg.FpgaAlteraEn) begin
        for (int k = 0; k < NR_READ_PORTS; k++) begin : block_read
          mem_read_sync[j][k] = mem[j][raddr_i[k]];  // synchronous RAM
          read_after_write[j][k] <= '0;
          if (waddr_i[j] == raddr_i[k])
            read_after_write[j][k] <= we_i[j] && ~waddr_i[j] != 0; // Identify if we need to read the content that was written
        end
      end
    end
    for (genvar k = 0; k < NR_READ_PORTS; k++) begin : block_read
      assign mem_read[j][k] = CVA6Cfg.FpgaAlteraEn ? ( read_after_write[j][k] ? wdata_reg[j]: mem_read_sync[j][k]) : mem[j][raddr_i[k]];
    end
  end
  //with synchronous ram there is the need to adjust which address is used at the output MUX
  assign raddr = CVA6Cfg.FpgaAlteraEn ? raddr_q : raddr_i;

  // output MUX
  logic [NR_READ_PORTS-1:0][LOG_NR_WRITE_PORTS-1:0] block_addr;
  for (genvar k = 0; k < NR_READ_PORTS; k++) begin : regfile_read_port
    assign block_addr[k] = mem_block_sel_q[raddr[k]];
    assign rdata_o[k] = (ZERO_REG_ZERO && raddr[k] == '0) ? '0 : mem_read[block_addr[k]][k];
  end

  // random initialization of the memory to suppress assert warnings on Questa.
  initial begin
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      for (int j = 0; j < NUM_WORDS; j++) begin
        if (!CVA6Cfg.FpgaAlteraEn)
          mem[i][j] = $random();  //quartus does not support this random statement on synthesis
        else mem[i][j] = '0;
      end
    end
  end

endmodule


module tb_ariane_regfile_fpga();

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
    if (rdata_o[0] == 32'hDEADBEEF) else $stop;

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
    if(rdata_o[0] == 32'hCAFEBABE) else $stop;
    if(rdata_o[1] == 32'hBAADF00D) else $stop;

    // More test cases can be added here

    $finish;
  end

endmodule
