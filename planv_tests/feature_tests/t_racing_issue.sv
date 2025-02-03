

module dut (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        in_valid,
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);

  logic [31:0] data_n, data_q;

  always_comb begin
    data_n = data_q;
    if (in_valid) data_n = in_data;
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      data_q <= '0;
    end else begin
      data_q <= data_n;
    end
  end

endmodule

module t_racing_issue;

  parameter CLK_PERIOD = 10;
  parameter NUM_ENTRIES = 10; // Number of test entries

  logic clk, rst_n;
  logic in_valid;
  logic [31:0] in_data;
  logic [31:0] out_data;

  dut uut (
    .clk(clk),
    .rst_n(rst_n),
    .in_valid(in_valid),
    .in_data(in_data),
    .out_data(out_data)
  );

  always # (CLK_PERIOD / 2) clk = ~clk;

  initial begin
    // Initialize signals
    clk = 0;
    rst_n = 0;
    in_valid = 0;
    in_data = '0;

    // Reset
    # (2 * CLK_PERIOD);
    rst_n = 1;

    // Apply test stimulus
    for (int i = 0; i < NUM_ENTRIES; i++) begin
      in_data = $random;
      in_valid = 1;
      # (CLK_PERIOD);
      in_valid = 0;
    end

    // Successful execution marker
    $write("*-* All Finished *-*");
    $finish;
  end

endmodule
