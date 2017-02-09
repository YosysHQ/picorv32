module testbench;
	reg clk = 1;
	always #5 clk = ~clk;

	reg resetn = 0;
	always @(posedge clk) resetn <= 1;

	wire        trap;
	wire        mem_valid;
	wire        mem_instr;
	reg         mem_ready;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0]  mem_wstrb;
	reg  [31:0] mem_rdata;

	picorv32 UUT (
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

	// 4096 32bit words = 16kB memory
	localparam MEM_SIZE = 4096;

	reg [31:0] memory [0:MEM_SIZE-1];
	initial $readmemh("firmware.hex", memory);

	always @(posedge clk) begin
		mem_ready <= 0;
		mem_rdata <= 'bx;

		if (resetn && mem_valid && !mem_ready) begin
			mem_ready <= 1;
			if (mem_wstrb) begin
				if (mem_addr == 32'h1000_0000) begin
					$write("%c", mem_wdata[7:0]);
					$fflush;
				end else begin
					if (mem_wstrb[0]) memory[mem_addr >> 2][ 7: 0] <= mem_wdata[ 7: 0];
					if (mem_wstrb[1]) memory[mem_addr >> 2][15: 8] <= mem_wdata[15: 8];
					if (mem_wstrb[2]) memory[mem_addr >> 2][23:16] <= mem_wdata[23:16];
					if (mem_wstrb[3]) memory[mem_addr >> 2][31:24] <= mem_wdata[31:24];
				end
			end else begin
				mem_rdata <= memory[mem_addr >> 2];
			end
		end

		if (resetn && trap) begin
			$display("TRAP.");
			$finish;
		end
	end

	initial begin
		$dumpfile("testbench.vcd");
		$dumpvars(0, testbench);
	end
endmodule

module picorv32_regs (
	input [4:0] A1ADDR, A2ADDR, B1ADDR,
	output reg [31:0] A1DATA, A2DATA,
	input [31:0] B1DATA,
	input B1EN, CLK1
);
	reg [31:0] memory [0:31];
	always @(posedge CLK1) begin
		A1DATA <= memory[A1ADDR];
		A2DATA <= memory[A2ADDR];
		if (B1EN) memory[B1ADDR] <= B1DATA;
	end
endmodule
