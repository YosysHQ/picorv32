module testbench(input clk, mem_ready_0, mem_ready_1);
	// set this to 1 to test generation of counter examples
	localparam ENABLE_COUNTERS = 0;

	reg resetn = 0;
	always @(posedge clk) resetn <= 1;

	(* keep *) wire trap_0, trace_valid_0, mem_valid_0, mem_instr_0;
	(* keep *) wire [3:0] mem_wstrb_0;
	(* keep *) wire [31:0] mem_addr_0, mem_wdata_0, mem_rdata_0;
	(* keep *) wire [35:0] trace_data_0;

	(* keep *) wire trap_1, trace_valid_1, mem_valid_1, mem_instr_1;
	(* keep *) wire [3:0] mem_wstrb_1;
	(* keep *) wire [31:0] mem_addr_1, mem_wdata_1, mem_rdata_1;
	(* keep *) wire [35:0] trace_data_1;

	reg [31:0] mem_0 [0:2**30-1];
	reg [31:0] mem_1 [0:2**30-1];

	assign mem_rdata_0 = mem_0[mem_addr_0 >> 2];
	assign mem_rdata_1 = mem_1[mem_addr_1 >> 2];

	always @(posedge clk) begin
		if (resetn && mem_valid_0 && mem_ready_0) begin
			if (mem_wstrb_0[3]) mem_0[mem_addr_0 >> 2][31:24] <= mem_wdata_0[31:24];
			if (mem_wstrb_0[2]) mem_0[mem_addr_0 >> 2][23:16] <= mem_wdata_0[23:16];
			if (mem_wstrb_0[1]) mem_0[mem_addr_0 >> 2][15: 8] <= mem_wdata_0[15: 8];
			if (mem_wstrb_0[0]) mem_0[mem_addr_0 >> 2][ 7: 0] <= mem_wdata_0[ 7: 0];
		end
		if (resetn && mem_valid_1 && mem_ready_1) begin
			if (mem_wstrb_1[3]) mem_1[mem_addr_1 >> 2][31:24] <= mem_wdata_1[31:24];
			if (mem_wstrb_1[2]) mem_1[mem_addr_1 >> 2][23:16] <= mem_wdata_1[23:16];
			if (mem_wstrb_1[1]) mem_1[mem_addr_1 >> 2][15: 8] <= mem_wdata_1[15: 8];
			if (mem_wstrb_1[0]) mem_1[mem_addr_1 >> 2][ 7: 0] <= mem_wdata_1[ 7: 0];
		end
	end

	(* keep *) reg [7:0] trace_balance;
	reg [7:0] trace_balance_q;

	always @* begin
		trace_balance = trace_balance_q;
		if (trace_valid_0) trace_balance = trace_balance + 1;
		if (trace_valid_1) trace_balance = trace_balance - 1;
	end

	always @(posedge clk) begin
		trace_balance_q <= resetn ? trace_balance : 0;
	end

	picorv32 #(
		// do not change this settings
		.ENABLE_COUNTERS(ENABLE_COUNTERS),
		.ENABLE_TRACE(1),

		// change this settings as you like
		.ENABLE_REGS_DUALPORT(1),
		.TWO_STAGE_SHIFT(1),
		.BARREL_SHIFTER(0),
		.TWO_CYCLE_COMPARE(0),
		.TWO_CYCLE_ALU(0),
		.COMPRESSED_ISA(0),
		.ENABLE_MUL(0),
		.ENABLE_DIV(0)
	) cpu_0 (
		.clk         (clk          ),
		.resetn      (resetn       ),
		.trap        (trap_0       ),
		.mem_valid   (mem_valid_0  ),
		.mem_instr   (mem_instr_0  ),
		.mem_ready   (mem_ready_0  ),
		.mem_addr    (mem_addr_0   ),
		.mem_wdata   (mem_wdata_0  ),
		.mem_wstrb   (mem_wstrb_0  ),
		.mem_rdata   (mem_rdata_0  ),
		.trace_valid (trace_valid_0),
		.trace_data  (trace_data_0 )
	);

	picorv32 #(
		// do not change this settings
		.ENABLE_COUNTERS(ENABLE_COUNTERS),
		.ENABLE_TRACE(1),

		// change this settings as you like
		.ENABLE_REGS_DUALPORT(1),
		.TWO_STAGE_SHIFT(1),
		.BARREL_SHIFTER(0),
		.TWO_CYCLE_COMPARE(0),
		.TWO_CYCLE_ALU(0),
		.COMPRESSED_ISA(0),
		.ENABLE_MUL(0),
		.ENABLE_DIV(0)
	) cpu_1 (
		.clk         (clk          ),
		.resetn      (resetn       ),
		.trap        (trap_1       ),
		.mem_valid   (mem_valid_1  ),
		.mem_instr   (mem_instr_1  ),
		.mem_ready   (mem_ready_1  ),
		.mem_addr    (mem_addr_1   ),
		.mem_wdata   (mem_wdata_1  ),
		.mem_wstrb   (mem_wstrb_1  ),
		.mem_rdata   (mem_rdata_1  ),
		.trace_valid (trace_valid_1),
		.trace_data  (trace_data_1 )
	);
endmodule
