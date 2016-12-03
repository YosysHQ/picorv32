module testbench(input clk, mem_ready_0, mem_ready_1);

	reg resetn = 0;

	always @(posedge clk)
		resetn <= 1;

	reg          pcpi_valid_0 = 1;
	reg          pcpi_valid_1 = 1;

	wire [31:0] pcpi_insn = $anyconst;
	wire [31:0] pcpi_rs1 = $anyconst;
	wire [31:0] pcpi_rs2 = $anyconst;

	wire        pcpi_wr_0;
	wire [31:0] pcpi_rd_0;
	wire        pcpi_wait_0;
	wire        pcpi_ready_0;

	wire        pcpi_wr_1;
	wire [31:0] pcpi_rd_1;
	wire        pcpi_wait_1;
	wire        pcpi_ready_1;

	reg         pcpi_wr_ref;
	reg  [31:0] pcpi_rd_ref;
	reg         pcpi_ready_ref = 0;

	picorv32_pcpi_mul mul_0 (
		.clk       (clk         ),
		.resetn    (resetn      ),
		.pcpi_valid(pcpi_valid_0),
		.pcpi_insn (pcpi_insn   ),
		.pcpi_rs1  (pcpi_rs1    ),
		.pcpi_rs2  (pcpi_rs2    ),
		.pcpi_wr   (pcpi_wr_0   ),
		.pcpi_rd   (pcpi_rd_0   ),
		.pcpi_wait (pcpi_wait_0 ),
		.pcpi_ready(pcpi_ready_0),

	);

	picorv32_pcpi_fast_mul mul_1 (
		.clk       (clk         ),
		.resetn    (resetn      ),
		.pcpi_valid(pcpi_valid_1),
		.pcpi_insn (pcpi_insn   ),
		.pcpi_rs1  (pcpi_rs1    ),
		.pcpi_rs2  (pcpi_rs2    ),
		.pcpi_wr   (pcpi_wr_1   ),
		.pcpi_rd   (pcpi_rd_1   ),
		.pcpi_wait (pcpi_wait_1 ),
		.pcpi_ready(pcpi_ready_1),

	);

	always @(posedge clk) begin
		if (resetn) begin
			if (pcpi_ready_0 && pcpi_ready_1) begin
				assert(pcpi_wr_0 == pcpi_wr_1);
				assert(pcpi_rd_0 == pcpi_rd_1);
			end

			if (pcpi_ready_0) begin
				pcpi_valid_0 <= 0;
				pcpi_wr_ref <= pcpi_wr_0;
				pcpi_rd_ref <= pcpi_rd_0;
				pcpi_ready_ref <= 1;
				if (pcpi_ready_ref) begin
					assert(pcpi_wr_0 == pcpi_wr_ref);
					assert(pcpi_rd_0 == pcpi_rd_ref);
				end
			end

			if (pcpi_ready_1) begin
				pcpi_valid_1 <= 0;
				pcpi_wr_ref <= pcpi_wr_1;
				pcpi_rd_ref <= pcpi_rd_1;
				pcpi_ready_ref <= 1;
				if (pcpi_ready_ref) begin
					assert(pcpi_wr_1 == pcpi_wr_ref);
					assert(pcpi_rd_1 == pcpi_rd_ref);
				end
			end
		end
	end
endmodule
