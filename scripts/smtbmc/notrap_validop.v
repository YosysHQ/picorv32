module testbench(input clk, mem_ready);
	`include "opcode.v"

	reg resetn = 0;
	always @(posedge clk) resetn <= 1;

	(* keep *) wire trap, mem_valid, mem_instr;
	(* keep *) wire [3:0] mem_wstrb;
	(* keep *) wire [31:0] mem_addr, mem_wdata, mem_rdata;
	(* keep *) wire [35:0] trace_data;

	reg [31:0] mem [0:2**30-1];

	assign mem_rdata = mem[mem_addr >> 2];

	always @(posedge clk) begin
		if (resetn && mem_valid && mem_ready) begin
			if (mem_wstrb[3]) mem[mem_addr >> 2][31:24] <= mem_wdata[31:24];
			if (mem_wstrb[2]) mem[mem_addr >> 2][23:16] <= mem_wdata[23:16];
			if (mem_wstrb[1]) mem[mem_addr >> 2][15: 8] <= mem_wdata[15: 8];
			if (mem_wstrb[0]) mem[mem_addr >> 2][ 7: 0] <= mem_wdata[ 7: 0];
		end
	end

	reg [1:0] mem_ready_stall = 0;

	always @(posedge clk) begin
		mem_ready_stall <= {mem_ready_stall, mem_valid && !mem_ready};
		restrict(&mem_ready_stall == 0);

		if (mem_instr && mem_ready && mem_valid) begin
			assume(opcode_valid(mem_rdata));
			assume(!opcode_branch(mem_rdata));
			assume(!opcode_load(mem_rdata));
			assume(!opcode_store(mem_rdata));
		end

		if (!mem_valid)
			assume(!mem_ready);

		if (resetn)
			assert(!trap);
	end

	picorv32 #(
		// change this settings as you like
		.ENABLE_REGS_DUALPORT(1),
		.TWO_STAGE_SHIFT(1),
		.BARREL_SHIFTER(0),
		.TWO_CYCLE_COMPARE(0),
		.TWO_CYCLE_ALU(0),
		.COMPRESSED_ISA(0),
		.ENABLE_MUL(0),
		.ENABLE_DIV(0)
	) cpu (
		.clk         (clk        ),
		.resetn      (resetn     ),
		.trap        (trap       ),
		.mem_valid   (mem_valid  ),
		.mem_instr   (mem_instr  ),
		.mem_ready   (mem_ready  ),
		.mem_addr    (mem_addr   ),
		.mem_wdata   (mem_wdata  ),
		.mem_wstrb   (mem_wstrb  ),
		.mem_rdata   (mem_rdata  )
	);
endmodule
