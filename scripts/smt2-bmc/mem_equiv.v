`timescale 1 ns / 1 ps

module main (input clk, resetn, domem, output trap);
	parameter integer MEMORY_WORDS = 2**30;
	parameter [0:0] ENABLE_REGS_DUALPORT = 1;
	parameter [0:0] TWO_STAGE_SHIFT = 1;
	parameter [0:0] TWO_CYCLE_COMPARE = 0;
	parameter [0:0] TWO_CYCLE_ALU = 0;

	(* keep *) wire mem_valid;
	(* keep *) wire mem_ready;
	(* keep *) wire [31:0] mem_addr;
	(* keep *) wire [31:0] mem_wdata;
	(* keep *) wire [ 3:0] mem_wstrb;
	(* keep *) wire [31:0] mem_rdata;

	picorv32 #(
		.ENABLE_REGS_DUALPORT(ENABLE_REGS_DUALPORT),
		.TWO_STAGE_SHIFT     (TWO_STAGE_SHIFT     ),
		.TWO_CYCLE_COMPARE   (TWO_CYCLE_COMPARE   ),
		.TWO_CYCLE_ALU       (TWO_CYCLE_ALU       )
	) cpu (
		.clk      (clk      ),
		.resetn   (resetn   ),
		.trap     (trap     ),
		.mem_valid(mem_valid),
		.mem_ready(mem_ready),
		.mem_addr (mem_addr ),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.mem_rdata(mem_rdata)
	);

	reg [31:0] memory [0:MEMORY_WORDS-1];

	assign mem_ready = domem && resetn && mem_valid;
	assign mem_rdata = memory[mem_addr >> 2];

	always @(posedge clk) begin
		if (mem_ready && mem_valid) begin
			if (mem_wstrb[0]) memory[mem_addr >> 2][ 7: 0] <= mem_wdata[ 7: 0];
			if (mem_wstrb[1]) memory[mem_addr >> 2][15: 8] <= mem_wdata[15: 8];
			if (mem_wstrb[2]) memory[mem_addr >> 2][23:16] <= mem_wdata[23:16];
			if (mem_wstrb[3]) memory[mem_addr >> 2][31:24] <= mem_wdata[31:24];
		end
	end
endmodule
