`timescale 1 ns / 1 ps

module test_soc (
	input         clk,
	input         resetn,
	output        trap,
	output [7:0]  out_byte,
	output reg    out_byte_en,

	output        monitor_valid,
	output [31:0] monitor_addr,
	output [31:0] monitor_data
);
	// 4096 32bit words = 16kB memory
	parameter MEM_SIZE = 4096;

	wire mem_valid;
	wire mem_instr;
	wire mem_ready;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0] mem_wstrb;
	reg [31:0] mem_rdata;

	wire mem_la_read;
	wire mem_la_write;
	wire [31:0] mem_la_addr;
	wire [31:0] mem_la_wdata;
	wire [3:0] mem_la_wstrb;

	picorv32 uut (
		.clk         (clk         ),
		.resetn      (resetn      ),
		.trap        (trap        ),
		.mem_valid   (mem_valid   ),
		.mem_instr   (mem_instr   ),
		.mem_ready   (mem_ready   ),
		.mem_addr    (mem_addr    ),
		.mem_wdata   (mem_wdata   ),
		.mem_wstrb   (mem_wstrb   ),
		.mem_rdata   (mem_rdata   ),
		.mem_la_read (mem_la_read ),
		.mem_la_write(mem_la_write),
		.mem_la_addr (mem_la_addr ),
		.mem_la_wdata(mem_la_wdata),
		.mem_la_wstrb(mem_la_wstrb)
	);

	assign monitor_valid = mem_valid;
	assign monitor_addr = mem_addr;
	assign monitor_data = mem_wstrb ? mem_wdata : mem_rdata;

	reg [31:0] memory [0:MEM_SIZE-1];
	initial $readmemh("firmware.hex", memory);

	assign mem_ready = 1;
	assign out_byte = mem_wdata[7:0];

	always @(posedge clk) begin
		out_byte_en <= 0;
		mem_rdata <= memory[mem_la_addr >> 2];
		if (mem_la_write && (mem_la_addr >> 2) < MEM_SIZE) begin
			if (mem_la_wstrb[0]) memory[mem_la_addr >> 2][ 7: 0] <= mem_la_wdata[ 7: 0];
			if (mem_la_wstrb[1]) memory[mem_la_addr >> 2][15: 8] <= mem_la_wdata[15: 8];
			if (mem_la_wstrb[2]) memory[mem_la_addr >> 2][23:16] <= mem_la_wdata[23:16];
			if (mem_la_wstrb[3]) memory[mem_la_addr >> 2][31:24] <= mem_la_wdata[31:24];
		end
		else
		if (mem_la_write && mem_la_addr == 32'h1000_0000) begin
			out_byte_en <= 1;
		end
	end
endmodule
