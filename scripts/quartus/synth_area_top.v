
module top_small (
	input clk, resetn,

	output        mem_valid,
	output        mem_instr,
	input         mem_ready,

	output [31:0] mem_addr,
	output [31:0] mem_wdata,
	output [ 3:0] mem_wstrb,
	input  [31:0] mem_rdata
);
	picorv32 #(
		.ENABLE_COUNTERS(0),
		.LATCHED_MEM_RDATA(1),
		.TWO_STAGE_SHIFT(0),
		.CATCH_MISALIGN(0),
		.CATCH_ILLINSN(0)
	) picorv32 (
		.clk      (clk      ),
		.resetn   (resetn   ),
		.mem_valid(mem_valid),
		.mem_instr(mem_instr),
		.mem_ready(mem_ready),
		.mem_addr (mem_addr ),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.mem_rdata(mem_rdata)
	);
endmodule

module top_regular (
	input clk, resetn,
	output trap,

	output        mem_valid,
	output        mem_instr,
	input         mem_ready,

	output [31:0] mem_addr,
	output [31:0] mem_wdata,
	output [ 3:0] mem_wstrb,
	input  [31:0] mem_rdata,

	// Look-Ahead Interface
	output        mem_la_read,
	output        mem_la_write,
	output [31:0] mem_la_addr,
	output [31:0] mem_la_wdata,
	output [ 3:0] mem_la_wstrb
);
	picorv32 picorv32 (
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
endmodule

module top_large (
	input clk, resetn,
	output trap,

	output        mem_valid,
	output        mem_instr,
	input         mem_ready,

	output [31:0] mem_addr,
	output [31:0] mem_wdata,
	output [ 3:0] mem_wstrb,
	input  [31:0] mem_rdata,

	// Look-Ahead Interface
	output        mem_la_read,
	output        mem_la_write,
	output [31:0] mem_la_addr,
	output [31:0] mem_la_wdata,
	output [ 3:0] mem_la_wstrb,

	// Pico Co-Processor Interface (PCPI)
	output        pcpi_valid,
	output [31:0] pcpi_insn,
	output [31:0] pcpi_rs1,
	output [31:0] pcpi_rs2,
	input         pcpi_wr,
	input  [31:0] pcpi_rd,
	input         pcpi_wait,
	input         pcpi_ready,

	// IRQ Interface
	input  [31:0] irq,
	output [31:0] eoi
);
	picorv32 #(
		.COMPRESSED_ISA(1),
		.BARREL_SHIFTER(1),
		.ENABLE_PCPI(1),
		.ENABLE_MUL(1),
		.ENABLE_IRQ(1)
	) picorv32 (
		.clk            (clk            ),
		.resetn         (resetn         ),
		.trap           (trap           ),
		.mem_valid      (mem_valid      ),
		.mem_instr      (mem_instr      ),
		.mem_ready      (mem_ready      ),
		.mem_addr       (mem_addr       ),
		.mem_wdata      (mem_wdata      ),
		.mem_wstrb      (mem_wstrb      ),
		.mem_rdata      (mem_rdata      ),
		.mem_la_read    (mem_la_read    ),
		.mem_la_write   (mem_la_write   ),
		.mem_la_addr    (mem_la_addr    ),
		.mem_la_wdata   (mem_la_wdata   ),
		.mem_la_wstrb   (mem_la_wstrb   ),
		.pcpi_valid     (pcpi_valid     ),
		.pcpi_insn      (pcpi_insn      ),
		.pcpi_rs1       (pcpi_rs1       ),
		.pcpi_rs2       (pcpi_rs2       ),
		.pcpi_wr        (pcpi_wr        ),
		.pcpi_rd        (pcpi_rd        ),
		.pcpi_wait      (pcpi_wait      ),
		.pcpi_ready     (pcpi_ready     ),
		.irq            (irq            ),
		.eoi            (eoi            )
	);
endmodule

