`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company:
// Engineer:
//
// Create Date: 16.05.2020 15:24:36
// Design Name:
// Module Name: basys3
// Project Name:
// Target Devices:
// Tool Versions:
// Description:
//
// Dependencies:
//
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//
//////////////////////////////////////////////////////////////////////////////////


module basys3(
    input clk,

    output RsTx,
    input RsRx,

    output [15:0] led);

	wire [0:5] CLKOUT;
    wire CLKFB;
    wire LOCKED;
    // Use PLL to easily change clock speeds
    PLLE2_BASE #(
       .CLKFBOUT_MULT(8),        // Multiply value for all CLKOUT, (2-64)
       .CLKFBOUT_PHASE(0.0),     // Phase offset in degrees of CLKFB, (-360.000-360.000).
       .CLKIN1_PERIOD(10),      // Input clock period in ns to ps resolution (i.e. 33.333 is 30 MHz).
       // CLKOUT0_DIVIDE - CLKOUT5_DIVIDE: Divide amount for each CLKOUT (1-128)
       .CLKOUT0_DIVIDE(16),
       .CLKOUT1_DIVIDE(16),
       .CLKOUT2_DIVIDE(16),
       .CLKOUT3_DIVIDE(16),
       .CLKOUT4_DIVIDE(16),
       .CLKOUT5_DIVIDE(16),
       // CLKOUT0_DUTY_CYCLE - CLKOUT5_DUTY_CYCLE: Duty cycle for each CLKOUT (0.001-0.999).
       .CLKOUT0_DUTY_CYCLE(0.5),
       .CLKOUT1_DUTY_CYCLE(0.5),
       .CLKOUT2_DUTY_CYCLE(0.5),
       .CLKOUT3_DUTY_CYCLE(0.5),
       .CLKOUT4_DUTY_CYCLE(0.5),
       .CLKOUT5_DUTY_CYCLE(0.5),
       // CLKOUT0_PHASE - CLKOUT5_PHASE: Phase offset for each CLKOUT (-360.000-360.000).
       .CLKOUT0_PHASE(0.0),
       .CLKOUT1_PHASE(0.0),
       .CLKOUT2_PHASE(0.0),
       .CLKOUT3_PHASE(0.0),
       .CLKOUT4_PHASE(0.0),
       .CLKOUT5_PHASE(0.0),
       .DIVCLK_DIVIDE(1)        // Master division value, (1-56)
    )
    PLLE2_BASE_inst (
       // Clock Outputs: 1-bit (each) output: User configurable clock outputs
       .CLKOUT0(CLKOUT[0]),   // 1-bit output: CLKOUT0
       .CLKOUT1(CLKOUT[1]),   // 1-bit output: CLKOUT1
       .CLKOUT2(CLKOUT[2]),   // 1-bit output: CLKOUT2
       .CLKOUT3(CLKOUT[3]),   // 1-bit output: CLKOUT3
       .CLKOUT4(CLKOUT[4]),   // 1-bit output: CLKOUT4
       .CLKOUT5(CLKOUT[5]),   // 1-bit output: CLKOUT5
       // Feedback Clocks: 1-bit (each) output: Clock feedback ports
       .CLKFBOUT(CLKFB), // 1-bit output: Feedback clock
       .LOCKED(LOCKED),     // 1-bit output: LOCK
       .CLKIN1(clk),     // 1-bit input: Input clock
       // Control Ports: 1-bit (each) input: PLL control ports
       //.PWRDWN(PWRDWN),     // 1-bit input: Power-down
       //.RST(RST),           // 1-bit input: Reset
       .CLKFBIN(CLKFB)    // 1-bit input: Feedback clock
    );


    reg [5:0] reset_cnt = 0;
    wire resetn = &reset_cnt;

    always @(posedge CLKOUT[0]) begin
        reset_cnt <= reset_cnt + !resetn;
    end

    wire iomem_valid;
    reg iomem_ready;
    wire [3:0] iomem_wstrb;
    wire [31:0] iomem_addr;
    wire [31:0] iomem_wdata;
    reg [31:0] iomem_rdata;

    reg [31:0] gpio = 0;

    assign led = gpio;

    always @(posedge CLKOUT[0]) begin
        if (!resetn) begin
            gpio <= 0;
        end else begin
            iomem_ready <= 0;
            if (iomem_valid && !iomem_ready && iomem_addr[31:24] == 8'h03) begin
                iomem_ready <= 1;
                iomem_rdata <= gpio;
                if (iomem_wstrb[0]) gpio[ 7: 0] <= iomem_wdata[ 7: 0];
                if (iomem_wstrb[1]) gpio[15: 8] <= iomem_wdata[15: 8];
                if (iomem_wstrb[2]) gpio[23:16] <= iomem_wdata[23:16];
				if (iomem_wstrb[3]) gpio[31:24] <= iomem_wdata[31:24];
			end
		end
	end

	picoramsoc #(
	   .ENABLE_MULDIV(0),
	   .ENABLE_COMPRESSED(0)
	) soc (
	   .clk(CLKOUT[0]),
	   .resetn(resetn),

	   .ser_tx(RsTx),
	   .ser_rx(RsRx),

	   .iomem_valid(iomem_valid),
	   .iomem_ready(iomem_ready),
	   .iomem_wstrb(iomem_wstrb),
	   .iomem_addr(iomem_addr),
	   .iomem_wdata(iomem_wdata),
	   .iomem_rdata(iomem_rdata));
endmodule
