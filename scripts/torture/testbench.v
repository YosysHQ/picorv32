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
	wire trap;

	wire        mem_valid;
	wire        mem_instr;
	reg         mem_ready;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0]  mem_wstrb;
	reg  [31:0] mem_rdata;

	wire        mem_la_read;
	wire        mem_la_write;
	wire [31:0] mem_la_addr;
	wire [31:0] mem_la_wdata;
	wire [3:0]  mem_la_wstrb;

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
`include "config.vh"
	) uut (
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

	localparam integer filename_len = 18;
	reg [8*filename_len-1:0] hex_filename;
	reg [8*filename_len-1:0] ref_filename;

	reg [31:0] memory [0:4095];
	reg [31:0] memory_ref [0:4095];
	integer i, errcount;
	integer cycle = 0;

	initial begin
		if ($value$plusargs("hex=%s", hex_filename)) $readmemh(hex_filename, memory);
		if ($value$plusargs("ref=%s", ref_filename)) $readmemh(ref_filename, memory_ref);
`ifndef VERILATOR
		if ($test$plusargs("vcd")) begin
			$dumpfile("test.vcd");
			$dumpvars(0, testbench);
		end
`endif
	end

	always @(posedge clk) begin
		mem_ready <= 0;
		mem_rdata <= 'bx;

		if (!trap || !resetn) begin
			if (x32[0] && resetn) begin
				if (mem_la_read) begin
					mem_ready <= 1;
					mem_rdata <= memory[mem_la_addr >> 2];
				end else
				if (mem_la_write) begin
					mem_ready <= 1;
					if (mem_la_wstrb[0]) memory[mem_la_addr >> 2][ 7: 0] <= mem_la_wdata[ 7: 0];
					if (mem_la_wstrb[1]) memory[mem_la_addr >> 2][15: 8] <= mem_la_wdata[15: 8];
					if (mem_la_wstrb[2]) memory[mem_la_addr >> 2][23:16] <= mem_la_wdata[23:16];
					if (mem_la_wstrb[3]) memory[mem_la_addr >> 2][31:24] <= mem_la_wdata[31:24];
				end else
				if (mem_valid && !mem_ready) begin
					mem_ready <= 1;
					if (mem_wstrb) begin
						if (mem_wstrb[0]) memory[mem_addr >> 2][ 7: 0] <= mem_wdata[ 7: 0];
						if (mem_wstrb[1]) memory[mem_addr >> 2][15: 8] <= mem_wdata[15: 8];
						if (mem_wstrb[2]) memory[mem_addr >> 2][23:16] <= mem_wdata[23:16];
						if (mem_wstrb[3]) memory[mem_addr >> 2][31:24] <= mem_wdata[31:24];
					end else begin
						mem_rdata <= memory[mem_addr >> 2];
					end
				end
			end
		end else begin
			errcount = 0;
			for (i=0; i < 4096; i=i+1) begin
				if (memory[i] !== memory_ref[i]) begin
					$display("Signature check failed at %04x: mem=%08x ref=%08x", i << 2, memory[i], memory_ref[i]);
					errcount = errcount + 1;
				end
			end
			if (errcount)
				$display("FAILED: Got %1d errors for %1s => %1s!", errcount, hex_filename, ref_filename);
			else
				$display("PASSED %1s => %1s.", hex_filename, ref_filename);
			$finish;
		end

		if (cycle > 100000) begin
			$display("FAILED: Timeout!");
			$finish;
		end

		resetn <= cycle > 10;
		cycle <= cycle + 1;
	end
endmodule
