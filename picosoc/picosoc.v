/*
 *  PicoSoC - A simple example SoC using PicoRV32
 *
 *  Copyright (C) 2017  Clifford Wolf <clifford@clifford.at>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

module picosoc (
	input clk,
	input resetn,

	output        iomem_valid,
	input         iomem_ready,
	output [ 3:0] iomem_wstrb,
	output [31:0] iomem_addr,
	output [31:0] iomem_wdata,
	input  [31:0] iomem_rdata,

	output flash_csb,
	output flash_clk,

	output flash_io0_oe,
	output flash_io1_oe,
	output flash_io2_oe,
	output flash_io3_oe,

	output flash_io0_do,
	output flash_io1_do,
	output flash_io2_do,
	output flash_io3_do,

	input  flash_io0_di,
	input  flash_io1_di,
	input  flash_io2_di,
	input  flash_io3_di
);
	parameter integer MEM_WORDS = 256;
	parameter [31:0] STACKADDR = (4*MEM_WORDS);       // end of memory
	parameter [31:0] PROGADDR_RESET = 32'h 0110_0000; // 1 MB into flash

	wire mem_valid;
	wire mem_instr;
	wire mem_ready;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0] mem_wstrb;
	wire [31:0] mem_rdata;

	wire spimem_ready;
	wire [31:0] spimem_rdata;

	reg ram_ready;
	reg [31:0] ram_rdata;

	assign iomem_valid = mem_valid && (mem_addr[31:24] > 8'h 01);
	assign iomem_wstrb = mem_wstrb;
	assign iomem_addr = mem_addr;
	assign iomem_wdata = mem_wdata;

	assign mem_ready = (iomem_valid && iomem_ready) || spimem_ready || ram_ready;
	assign mem_rdata = (iomem_valid && iomem_ready) ? iomem_rdata : spimem_ready ? spimem_rdata : ram_ready ? ram_rdata : 32'h xxxx_xxxx;

	picorv32 #(
		.STACKADDR(STACKADDR),
		.PROGADDR_RESET(PROGADDR_RESET)
	) cpu (
		.clk         (clk        ),
		.resetn      (resetn     ),
		.mem_valid   (mem_valid  ),
		.mem_instr   (mem_instr  ),
		.mem_ready   (mem_ready  ),
		.mem_addr    (mem_addr   ),
		.mem_wdata   (mem_wdata  ),
		.mem_wstrb   (mem_wstrb  ),
		.mem_rdata   (mem_rdata  )
	);

	spimemio spimemio (
		.clk(clk),
		.resetn(resetn),
		.valid (mem_valid && mem_addr[31:24] == 8'h 01),
		.ready (spimem_ready),
		.addr  (mem_addr[23:0]),
		.rdata (spimem_rdata),

		.flash_csb (flash_csb),
		.flash_clk (flash_clk),

		.flash_io0 (flash_io0_do),
		.flash_io1 (flash_io1_di),
		.flash_io2 (flash_io2_di),
		.flash_io3 (flash_io3_di)
	);

	assign flash_io0_oe = 1;
	assign flash_io1_oe = 0;
	assign flash_io2_oe = 0;
	assign flash_io3_oe = 0;

	assign flash_io1_do = 0;
	assign flash_io2_do = 0;
	assign flash_io3_do = 0;

	reg [31:0] memory [0:MEM_WORDS-1];

	always @(posedge clk) begin
		ram_ready <= 0;
		if (mem_valid && !mem_ready && mem_addr[31:24] == 8'h 00) begin
			ram_ready <= 1;
			ram_rdata <= memory[mem_addr >> 2];
			if (mem_wstrb[0]) memory[mem_addr >> 2][ 7: 0] <= mem_wdata[ 7: 0];
			if (mem_wstrb[1]) memory[mem_addr >> 2][15: 8] <= mem_wdata[15: 8];
			if (mem_wstrb[2]) memory[mem_addr >> 2][23:16] <= mem_wdata[23:16];
			if (mem_wstrb[3]) memory[mem_addr >> 2][31:24] <= mem_wdata[31:24];
		end
	end
endmodule
