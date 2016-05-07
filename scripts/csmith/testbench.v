`timescale 1 ns / 1 ps

module testbench (
`ifdef VERILATOR
	input clk
`endif
);
`ifndef VERILATOR
	reg clk = 1;
	always #5 clk = ~clk;
`endif

	reg resetn = 0;
	integer resetn_cnt = 0;
	wire trap;

	initial begin
		// $dumpfile("testbench.vcd");
		// $dumpvars(0, testbench);
	end

	always @(posedge clk) begin
		if (resetn_cnt < 100)
			resetn_cnt <= resetn_cnt + 1;
		else
			resetn <= 1;
	end

	wire mem_valid;
	wire mem_instr;
	wire mem_ready;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0] mem_wstrb;
	wire [31:0] mem_rdata;

	reg [31:0] x32 = 314159265;
	reg [31:0] next_x32;

	always @(posedge clk) begin
		if (resetn) begin
			next_x32 = x32;
			next_x32 = next_x32 ^ (next_x32 << 13);
			next_x32 = next_x32 ^ (next_x32 >> 17);
			next_x32 = next_x32 ^ (next_x32 << 5);
			x32 <= next_x32;
		end
	end

	picorv32 #(
		.COMPRESSED_ISA(1),
		.ENABLE_MUL(1),
		.ENABLE_DIV(1)
	) uut (
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

	reg [7:0] memory [0:4*1024*1024-1];
	initial $readmemh("test.hex", memory);

	assign mem_ready = x32[0] && mem_valid;

	assign mem_rdata[ 7: 0] = memory[mem_addr + 0];
	assign mem_rdata[15: 8] = memory[mem_addr + 1];
	assign mem_rdata[23:16] = memory[mem_addr + 2];
	assign mem_rdata[31:24] = memory[mem_addr + 3];

	always @(posedge clk) begin
		if (mem_valid && mem_ready) begin
			if (mem_wstrb && mem_addr == 'h10000000) begin
				$write("%c", mem_wdata[ 7: 0]);
`ifndef VERILATOR
				$fflush;
`endif
			end else begin
				if (mem_wstrb[0]) memory[mem_addr + 0] <= mem_wdata[ 7: 0];
				if (mem_wstrb[1]) memory[mem_addr + 1] <= mem_wdata[15: 8];
				if (mem_wstrb[2]) memory[mem_addr + 2] <= mem_wdata[23:16];
				if (mem_wstrb[3]) memory[mem_addr + 3] <= mem_wdata[31:24];
			end
		end
	end

	always @(posedge clk) begin
		if (resetn && trap) begin
			// repeat (10) @(posedge clk);
			// $display("TRAP");
			$finish;
		end
	end
endmodule
