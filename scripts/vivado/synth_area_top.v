
module top_small (
	input clk, resetn,
	output trap,

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
		.ENABLE_REGS_16_31(0),
		.ENABLE_REGS_DUALPORT(1),
		.LATCHED_MEM_RDATA(1)
	) picorv32 (
		.clk      (clk      ),
		.resetn   (resetn   ),
		.trap     (trap     ),
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
	output        pcpi_insn_valid,
	output [31:0] pcpi_insn,
	output        pcpi_rs1_valid,
	output [31:0] pcpi_rs1,
	output        pcpi_rs2_valid,
	output [31:0] pcpi_rs2,
	input         pcpi_rd_valid,
	input  [31:0] pcpi_rd,
	input         pcpi_wait,
	input         pcpi_ready,

	// IRQ Interface
	input  [31:0] irq,
	output [31:0] eoi
);
	picorv32 #(
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
		.pcpi_insn_valid(pcpi_insn_valid),
		.pcpi_insn      (pcpi_insn      ),
		.pcpi_rs1_valid (pcpi_rs1_valid ),
		.pcpi_rs1       (pcpi_rs1       ),
		.pcpi_rs2_valid (pcpi_rs2_valid ),
		.pcpi_rs2       (pcpi_rs2       ),
		.pcpi_rd_valid  (pcpi_rd_valid  ),
		.pcpi_rd        (pcpi_rd        ),
		.pcpi_wait      (pcpi_wait      ),
		.pcpi_ready     (pcpi_ready     ),
		.irq            (irq            ),
		.eoi            (eoi            )
	);
endmodule

