//======================================================================
// trng_wrap.v
// Registers only the top-level read_data so it appears in SMT state.
// Set this wrapper as the synthesis top.
//======================================================================

`timescale 1ns / 100ps

module trng_wrap (
  // Clock and reset.
  input  wire         clk,
  input  wire         reset_n,

  input  wire         avalanche_noise,

  input  wire         cs,
  input  wire         we,
  input  wire  [11:0] address,
  input  wire  [31:0] write_data,

  // NOTE: registered to force inclusion in |main_s|
  (* keep = 1, public = "true" *)
  output reg  [31:0]  read_data,

  output wire         error,

  output wire  [7:0]  debug,
  input  wire         debug_update,

  output wire         security_error
);

  // Core's original combinational read_data
  wire [31:0] read_data_comb;
  reg  [31:0] read_data_state = 32'h0000_0000;
  // Instantiate the unmodified TRNG core from trng.v
  trng u_trng_core (
    .clk(clk),
    .reset_n(reset_n),

    .avalanche_noise(avalanche_noise),

    .cs(cs),
    .we(we),
    .address(address),
    .write_data(write_data),

    // tap the core's combinational result
    .read_data(read_data_comb),

    .error(error),

    .debug(debug),
    .debug_update(debug_update),

    .security_error(security_error)
  );
  // Register the output so Yosys treats it as sequential state.
  always @(posedge clk) begin
    read_data_state <= read_data_comb;
  end
  assign read_data = read_data_comb;
endmodule
