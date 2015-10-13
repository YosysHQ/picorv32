`timescale 1 ns / 1 ps

module top (
	input clk,
	output reg LED0, LED1, LED2, LED3, LED4, LED5, LED6, LED7
);
	// -------------------------------
	// Reset Generator

	reg [7:0] resetn_counter = 0;
	wire resetn = &resetn_counter;

	always @(posedge clk) begin
		if (!resetn)
			resetn_counter <= resetn_counter + 1;
	end


	// -------------------------------
	// PicoRV32 Core

	wire mem_valid;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0] mem_wstrb;

	reg mem_ready;
	reg [31:0] mem_rdata;

	picorv32 #(
		.ENABLE_COUNTERS(0),
		.LATCHED_MEM_RDATA(1),
		.TWO_STAGE_SHIFT(0),
		.TWO_CYCLE_ALU(1),
		.CATCH_MISALIGN(0),
		.CATCH_ILLINSN(0)
	) cpu (
		.clk      (clk      ),
		.resetn   (resetn   ),
		.mem_valid(mem_valid),
		.mem_ready(mem_ready),
		.mem_addr (mem_addr ),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.mem_rdata(mem_rdata)
	);


	// -------------------------------
	// Memory/IO Interface

	// 128 32bit words = 512 bytes memory
	localparam MEM_SIZE = 128;
	reg [31:0] memory [0:MEM_SIZE-1];
	initial $readmemh("firmware.hex", memory);

	always @(posedge clk) begin
		mem_ready <= 0;
		if (resetn && mem_valid && !mem_ready) begin
			(* parallel_case *)
			case (1)
				!mem_wstrb && (mem_addr >> 2) < MEM_SIZE: begin
					mem_rdata <= memory[mem_addr >> 2];
					mem_ready <= 1;
				end
				|mem_wstrb && (mem_addr >> 2) < MEM_SIZE: begin
					if (mem_wstrb[0]) memory[mem_addr >> 2][ 7: 0] <= mem_wdata[ 7: 0];
					if (mem_wstrb[1]) memory[mem_addr >> 2][15: 8] <= mem_wdata[15: 8];
					if (mem_wstrb[2]) memory[mem_addr >> 2][23:16] <= mem_wdata[23:16];
					if (mem_wstrb[3]) memory[mem_addr >> 2][31:24] <= mem_wdata[31:24];
					mem_ready <= 1;
				end
				|mem_wstrb && mem_addr == 32'h1000_0000: begin
					{LED7, LED6, LED5, LED4, LED3, LED2, LED1, LED0} <= mem_wdata;
					mem_ready <= 1;
				end
			endcase
		end
	end
endmodule
