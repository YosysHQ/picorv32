module testbench(
	input clk, mem_ready_0, mem_ready_1,
	input [31:0] mem_rdata
);
	// set this to 1 to test generation of counterexamples
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

	reg [31:0] last_mem_rdata;

	assign mem_rdata_0 = mem_rdata;
	assign mem_rdata_1 = mem_rdata;

	wire mem_xfer_0 = resetn && mem_valid_0 && mem_ready_0;
	wire mem_xfer_1 = resetn && mem_valid_1 && mem_ready_1;

	reg [1:0] cmp_mem_state = 0;
	reg [31:0] cmp_mem_addr;
	reg [31:0] cmp_mem_wdata;
	reg [3:0] cmp_mem_wstrb;

	always @* begin
		if (mem_valid_0 == 0)
			assume(!mem_ready_0 == 0);
		if (mem_valid_1 == 0)
			assume(mem_ready_1 == 0);
	end

	always @(posedge clk) begin
		if (cmp_mem_state)
			assume(last_mem_rdata == mem_rdata);
		last_mem_rdata <= mem_rdata;
	end

	always @(posedge clk) begin
		case (cmp_mem_state)
			2'b 00: begin
				case ({mem_xfer_1, mem_xfer_0})
					2'b 11: begin
						assert(mem_addr_0 == mem_addr_1);
						assert(mem_wstrb_0 == mem_wstrb_1);
						if (mem_wstrb_0[3]) assert(mem_wdata_0[31:24] == mem_wdata_1[31:24]);
						if (mem_wstrb_0[2]) assert(mem_wdata_0[23:16] == mem_wdata_1[23:16]);
						if (mem_wstrb_0[1]) assert(mem_wdata_0[15: 8] == mem_wdata_1[15: 8]);
						if (mem_wstrb_0[0]) assert(mem_wdata_0[ 7: 0] == mem_wdata_1[ 7: 0]);
					end
					2'b 01: begin
						cmp_mem_state <= 2'b 01;
						cmp_mem_addr <= mem_addr_0;
						cmp_mem_wdata <= mem_wdata_0;
						cmp_mem_wstrb <= mem_wstrb_0;
					end
					2'b 10: begin
						cmp_mem_state <= 2'b 10;
						cmp_mem_addr <= mem_addr_1;
						cmp_mem_wdata <= mem_wdata_1;
						cmp_mem_wstrb <= mem_wstrb_1;
					end
				endcase
			end
			2'b 01: begin
				assume(!mem_xfer_0);
				if (mem_xfer_1) begin
					cmp_mem_state <= 2'b 00;
					assert(cmp_mem_addr == mem_addr_1);
					assert(cmp_mem_wstrb == mem_wstrb_1);
					if (cmp_mem_wstrb[3]) assert(cmp_mem_wdata[31:24] == mem_wdata_1[31:24]);
					if (cmp_mem_wstrb[2]) assert(cmp_mem_wdata[23:16] == mem_wdata_1[23:16]);
					if (cmp_mem_wstrb[1]) assert(cmp_mem_wdata[15: 8] == mem_wdata_1[15: 8]);
					if (cmp_mem_wstrb[0]) assert(cmp_mem_wdata[ 7: 0] == mem_wdata_1[ 7: 0]);
				end
			end
			2'b 10: begin
				assume(!mem_xfer_1);
				if (mem_xfer_0) begin
					cmp_mem_state <= 2'b 00;
					assert(cmp_mem_addr == mem_addr_0);
					assert(cmp_mem_wstrb == mem_wstrb_0);
					if (cmp_mem_wstrb[3]) assert(cmp_mem_wdata[31:24] == mem_wdata_0[31:24]);
					if (cmp_mem_wstrb[2]) assert(cmp_mem_wdata[23:16] == mem_wdata_0[23:16]);
					if (cmp_mem_wstrb[1]) assert(cmp_mem_wdata[15: 8] == mem_wdata_0[15: 8]);
					if (cmp_mem_wstrb[0]) assert(cmp_mem_wdata[ 7: 0] == mem_wdata_0[ 7: 0]);
				end
			end
		endcase
	end

	reg [1:0] cmp_trace_state = 0;
	reg [35:0] cmp_trace_data;

	always @(posedge clk) begin
		if (resetn) begin
			case (cmp_trace_state)
				2'b 00: begin
					case ({trace_valid_1, trace_valid_0})
						2'b 11: begin
							assert(trace_data_0 == trace_data_1);
						end
						2'b 01: begin
							cmp_trace_state <= 2'b 01;
							cmp_trace_data <= trace_data_0;
						end
						2'b 10: begin
							cmp_trace_state <= 2'b 10;
							cmp_trace_data <= trace_data_1;
						end
					endcase
				end
				2'b 01: begin
					assume(!trace_valid_0);
					if (trace_valid_1) begin
						cmp_trace_state <= 2'b 00;
						assert(cmp_trace_data == trace_data_1);
					end
				end
				2'b 10: begin
					assume(!trace_valid_1);
					if (trace_valid_0) begin
						cmp_trace_state <= 2'b 00;
						assert(cmp_trace_data == trace_data_0);
					end
				end
			endcase
		end
	end

	picorv32 #(
		// do not change this settings
		.ENABLE_COUNTERS(ENABLE_COUNTERS),
		.ENABLE_TRACE(1),

		// change this settings as you like
		.ENABLE_REGS_DUALPORT(1),
		.TWO_STAGE_SHIFT(0),
		.BARREL_SHIFTER(0),
		.TWO_CYCLE_COMPARE(0),
		.TWO_CYCLE_ALU(0),
		.COMPRESSED_ISA(1),
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
		.COMPRESSED_ISA(1),
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
