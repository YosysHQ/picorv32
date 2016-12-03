// Based on the benchmark from 2016 Yosys-SMTBMC presentation, which in turn is
// based on the tracecmp2 test from this directory.

module testbench (
	input clk,
	input [31:0] mem_rdata_in,

	input             pcpi_wr,
	input      [31:0] pcpi_rd,
	input             pcpi_wait,
	input             pcpi_ready
);
	reg resetn = 0;

	always @(posedge clk)
		resetn <= 1;

	wire        cpu0_trap;
	wire        cpu0_mem_valid;
	wire        cpu0_mem_instr;
	wire        cpu0_mem_ready;
	wire [31:0] cpu0_mem_addr;
	wire [31:0] cpu0_mem_wdata;
	wire [3:0]  cpu0_mem_wstrb;
	wire [31:0] cpu0_mem_rdata;
	wire        cpu0_trace_valid;
	wire [35:0] cpu0_trace_data;

	wire        cpu1_trap;
	wire        cpu1_mem_valid;
	wire        cpu1_mem_instr;
	wire        cpu1_mem_ready;
	wire [31:0] cpu1_mem_addr;
	wire [31:0] cpu1_mem_wdata;
	wire [3:0]  cpu1_mem_wstrb;
	wire [31:0] cpu1_mem_rdata;
	wire        cpu1_trace_valid;
	wire [35:0] cpu1_trace_data;

	wire        mem_ready;
	wire [31:0] mem_rdata;

	assign mem_ready = cpu0_mem_valid && cpu1_mem_valid;
	assign mem_rdata = mem_rdata_in;

	assign cpu0_mem_ready = mem_ready;
	assign cpu0_mem_rdata = mem_rdata;

	assign cpu1_mem_ready = mem_ready;
	assign cpu1_mem_rdata = mem_rdata;

	reg [ 2:0] trace_balance = 3'b010;
	reg [35:0] trace_buffer_cpu0 = 0, trace_buffer_cpu1 = 0;

	always @(posedge clk) begin
		if (resetn) begin
			if (cpu0_trace_valid)
				trace_buffer_cpu0 <= cpu0_trace_data;

			if (cpu1_trace_valid)
				trace_buffer_cpu1 <= cpu1_trace_data;

			if (cpu0_trace_valid && !cpu1_trace_valid)
				trace_balance <= trace_balance << 1;

			if (!cpu0_trace_valid && cpu1_trace_valid)
				trace_balance <= trace_balance >> 1;
		end
	end

	always @* begin
		if (resetn && cpu0_mem_ready) begin
			assert(cpu0_mem_addr == cpu1_mem_addr);
			assert(cpu0_mem_wstrb == cpu1_mem_wstrb);
			if (cpu0_mem_wstrb[3]) assert(cpu0_mem_wdata[31:24] == cpu1_mem_wdata[31:24]);
			if (cpu0_mem_wstrb[2]) assert(cpu0_mem_wdata[23:16] == cpu1_mem_wdata[23:16]);
			if (cpu0_mem_wstrb[1]) assert(cpu0_mem_wdata[15: 8] == cpu1_mem_wdata[15: 8]);
			if (cpu0_mem_wstrb[0]) assert(cpu0_mem_wdata[ 7: 0] == cpu1_mem_wdata[ 7: 0]);
		end
		if (trace_balance == 3'b010) begin
			assert(trace_buffer_cpu0 == trace_buffer_cpu1);
		end
	end

	picorv32 #(
		.ENABLE_COUNTERS(0),
		.REGS_INIT_ZERO(1),
		.COMPRESSED_ISA(1),
		.ENABLE_TRACE(1),

		.TWO_STAGE_SHIFT(0),
		.ENABLE_PCPI(1)
	) cpu0 (
		.clk         (clk             ),
		.resetn      (resetn          ),
		.trap        (cpu0_trap       ),
		.mem_valid   (cpu0_mem_valid  ),
		.mem_instr   (cpu0_mem_instr  ),
		.mem_ready   (cpu0_mem_ready  ),
		.mem_addr    (cpu0_mem_addr   ),
		.mem_wdata   (cpu0_mem_wdata  ),
		.mem_wstrb   (cpu0_mem_wstrb  ),
		.mem_rdata   (cpu0_mem_rdata  ),
		.pcpi_wr     (pcpi_wr         ),
		.pcpi_rd     (pcpi_rd         ),
		.pcpi_wait   (pcpi_wait       ),
		.pcpi_ready  (pcpi_ready      ),
		.trace_valid (cpu0_trace_valid),
		.trace_data  (cpu0_trace_data )
	);

	picorv32 #(
		.ENABLE_COUNTERS(0),
		.REGS_INIT_ZERO(1),
		.COMPRESSED_ISA(1),
		.ENABLE_TRACE(1),

		.TWO_STAGE_SHIFT(1),
		.TWO_CYCLE_COMPARE(1),
		.TWO_CYCLE_ALU(1)
	) cpu1 (
		.clk         (clk             ),
		.resetn      (resetn          ),
		.trap        (cpu1_trap       ),
		.mem_valid   (cpu1_mem_valid  ),
		.mem_instr   (cpu1_mem_instr  ),
		.mem_ready   (cpu1_mem_ready  ),
		.mem_addr    (cpu1_mem_addr   ),
		.mem_wdata   (cpu1_mem_wdata  ),
		.mem_wstrb   (cpu1_mem_wstrb  ),
		.mem_rdata   (cpu1_mem_rdata  ),
		.trace_valid (cpu1_trace_valid),
		.trace_data  (cpu1_trace_data )
	);
endmodule
