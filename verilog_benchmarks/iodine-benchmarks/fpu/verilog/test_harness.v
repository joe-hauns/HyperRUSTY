// FILE: fdiv_harness.v
// A minimal test harness to expose the fdiv constant-time violation.

`timescale 1ns / 100ps

// Include only the necessary dependencies
`include "except.v"
`include "pre_norm_fmul.v"
// Assuming div_r2 is in primitives.v
`include "primitives.v"

module fdiv_harness(
    input           clk,
    input   [31:0]  opa,
    input   [31:0]  opb,
    output          done // Our new, explicit done signal
);

    // Internal wires to connect the modules
    wire    opb_00;         // From except: Is operand B zero?
    wire    [23:0]  fracta_mul;   // From pre_norm_fmul
    wire    [23:0]  fractb_mul;   // From pre_norm_fmul
    wire    [49:0]  quo;          // From div_r2
    wire    [49:0]  rem;          // From div_r2

    // For simplicity, we hardcode the fpu_op to DIV (3'b011)
    // and other inputs like rmode.
    localparam FPU_OP_DIV = 3'b011;

    // Registers for the inputs, mimicking the first pipeline stage
    reg [31:0] opa_r, opb_r;
    always @(posedge clk) begin
        opa_r <= opa;
        opb_r <= opb;
    end

    //=============== 1. Instantiate Essential Modules ===============

    // We need the 'except' module to detect if opb is zero.
    except u_except(
        .clk(clk),
        .opa(opa_r),
        .opb(opb_r),
        .opb_00(opb_00), // This is the signal that triggers the fast path
        // Other outputs are not needed for this test
        .inf(), .ind(), .qnan(), .snan(), .opa_nan(), .opb_nan(),
        .opa_00(), .opa_inf(), .opb_inf(), .opa_dn(), .opb_dn()
    );

    // We need the 'pre_norm_fmul' module to prepare operands for the slow path.
    pre_norm_fmul u_prenorm(
        .clk(clk),
        .fpu_op(FPU_OP_DIV),
        .opa(opa_r),
        .opb(opb_r),
        .fracta(fracta_mul),
        .fractb(fractb_mul),
        // Other outputs are not needed
        .exp_out(), .sign(), .sign_exe(), .inf(), .exp_ovf(), .underflow()
    );

    // We need the 'div_r2' module, which is the slow iterative divider.
    // NOTE: The 'div_r2' module takes many cycles. The exact number is
    // the latency of the slow path.
    div_r2 u_divider(
        .clk(clk),
        // The original design has complex logic for the 'opa' to the divider.
        // We simplify it here, as it's not essential for the timing leak.
        .opa({fracta_mul, 26'd0}),
        .opb(fractb_mul),
        .quo(quo),
        .rem(rem)
    );

    //=============== 2. Model the Timing Violation Explicitly ===============

    // The flaw is the data-dependent execution path. We model this with two
    // 'done' signals representing the fast and slow paths.

    // The FAST path finishes in just a few cycles if opb is zero.
    // We can model this with a simple pipeline delay.
    reg opb_00_r1, opb_00_r2;
    always @(posedge clk) begin
        opb_00_r1 <= opb_00;
        opb_00_r2 <= opb_00_r1;
    end
    wire done_fast = opb_00_r2; // Done in 2 cycles if opb is zero

    // The SLOW path takes as long as the 'div_r2' module.
    // The latency of div_r2 is fixed but long. Let's assume it's ~30 cycles.
    // We can model this with a counter.
    reg [5:0] slow_path_counter;
    reg done_slow_reg;

    always @(posedge clk) begin
        if (!opb_00) begin // Only start the counter for the slow path
            if (slow_path_counter == 30) begin
                done_slow_reg <= 1'b1;
                slow_path_counter <= 0;
            end else begin
                done_slow_reg <= 1'b0;
                slow_path_counter <= slow_path_counter + 1;
            end
        end else begin
            slow_path_counter <= 0;
            done_slow_reg <= 1'b0;
        end
    end
    wire done_slow = done_slow_reg;

    // The final 'done' signal depends on which path was taken.
    assign done = done_fast | done_slow;

endmodule