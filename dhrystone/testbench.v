`timescale 1 ns / 1 ps

module testbench;
	reg clk = 1;
	reg resetn = 0;
	wire trap;

	always #5 clk = ~clk;

	initial begin
		repeat (100) @(posedge clk);
		resetn <= 1;
	end

	wire mem_valid;
	wire mem_instr;
	wire mem_ready;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0] mem_wstrb;
	reg  [31:0] mem_rdata;
	wire mem_la_read;
	wire [31:0] mem_la_addr;

	picorv32 uut (
		.clk        (clk        ),
		.resetn     (resetn     ),
		.trap       (trap       ),
		.mem_valid  (mem_valid  ),
		.mem_instr  (mem_instr  ),
		.mem_ready  (mem_ready  ),
		.mem_addr   (mem_addr   ),
		.mem_wdata  (mem_wdata  ),
		.mem_wstrb  (mem_wstrb  ),
		.mem_rdata  (mem_rdata  ),
		.mem_la_read(mem_la_read),
		.mem_la_addr(mem_la_addr)
	);

	reg [31:0] memory [0:64*1024/4-1];
	initial $readmemh("dhry.hex", memory);

	assign mem_ready = 1;

	always @(posedge clk) begin
		mem_rdata <= mem_la_read ? memory[mem_la_addr >> 2] : 'bx;
		if (mem_valid) begin
			case (mem_addr)
				32'h1000_0000: begin
`ifndef INSN_TIMING
					$write("%c", mem_wdata);
					$fflush();
`endif
				end
				default: begin
					if (mem_wstrb[0]) memory[mem_addr >> 2][ 7: 0] <= mem_wdata[ 7: 0];
					if (mem_wstrb[1]) memory[mem_addr >> 2][15: 8] <= mem_wdata[15: 8];
					if (mem_wstrb[2]) memory[mem_addr >> 2][23:16] <= mem_wdata[23:16];
					if (mem_wstrb[3]) memory[mem_addr >> 2][31:24] <= mem_wdata[31:24];
				end
			endcase
		end
	end

	initial begin
		$dumpfile("testbench.vcd");
		$dumpvars(0, testbench);
	end

	always @(posedge clk) begin
		if (resetn && trap) begin
			repeat (10) @(posedge clk);
			$display("TRAP");
			$finish;
		end
	end

`ifdef INSN_TIMING
	initial begin
		repeat (100000) @(posedge clk);
		$finish;
	end
	always @(uut.count_instr[0]) begin
		//  iverilog -DINSN_TIMING testbench.v ../picorv32.v && ./a.out > x
		//  sed 's,.*## ,,' x | gawk 'x != "" {print x,$2-y;} {x=$1;y=$2;}' | sort | uniq -c | sort -k3 -n
		$display("## %-s %d", uut.instruction, uut.count_cycle);
	end
`endif
endmodule
