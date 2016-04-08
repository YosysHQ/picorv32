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

	picorv32 #(
		.COMPRESSED_ISA(1)
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
		.mem_rdata   (mem_rdata   )
	);

	reg [1023:0] hex_filename;
	reg [1023:0] ref_filename;

	reg [31:0] memory [0:4095];
	reg [31:0] memory_ref [0:4095];
	integer i, errcount;

	initial begin
		if ($value$plusargs("hex=%s", hex_filename)) $readmemh(hex_filename, memory);
		if ($value$plusargs("ref=%s", ref_filename)) $readmemh(ref_filename, memory_ref);
		// $dumpfile("testbench.vcd");
		// $dumpvars(0, testbench);

		repeat (10) @(posedge clk);
		resetn <= 1;
	end

	always @(posedge clk) begin
		mem_ready <= 0;
		mem_rdata <= 'bx;

		if (!trap || !resetn) begin
			if (mem_valid && !mem_ready && resetn) begin
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
		end else begin
			errcount = 0;
			for (i=0; i < 4096; i=i+1) begin
				if (memory[i] !== memory_ref[i]) begin
					$display("Signature check failed at %04x: mem=%08x ref=%08x", i << 2, memory[i], memory_ref[i]);
					errcount = errcount + 1;
				end
			end
			if (errcount)
				$display("FAILED: Got %1d errors for %1s/%1s!", errcount, hex_filename, ref_filename);
			else
				$display("PASSED %1s/%1s.", hex_filename, ref_filename);
			$finish;
		end
	end
endmodule
