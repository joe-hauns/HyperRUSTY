// fcmp_wrapper.v
`include "fcmp.v" // Include your original file

module fcmptop(
    // Inputs
    input clk,
    input rst,
    input [31:0] opa_in,
    input [31:0] opb_in,

    // Outputs
    output unordered,
    output altb,
    output blta,
    output aeqb,
    output inf,
    output zero
);

    // Registers to hold the state (inputs to the fcmp unit)
    reg [31:0] opa_reg, opb_reg;

    // This block creates flip-flops for the inputs
    always @(posedge clk) begin
        if (rst) begin
            opa_reg <= 32'b0;
            opb_reg <= 32'b0;
        end else begin
            opa_reg <= opa_in;
            opb_reg <= opb_in;
        end
    end

    // Instantiate your original combinational module
    fcmp u_fcmp (
        .opa(opa_reg),      // Use the registered inputs
        .opb(opb_reg),      // Use the registered inputs
        .unordered(unordered),
        .altb(altb),
        .blta(blta),
        .aeqb(aeqb),
        .inf(inf),
        .zero(zero)
    );

endmodule