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
	wire mem_la_write;
	wire [31:0] mem_la_addr;
	wire [31:0] mem_la_wdata;
	wire [3:0] mem_la_wstrb;

	picorv32 #(
		.BARREL_SHIFTER(1),
		.ENABLE_FAST_MUL(1),
		.ENABLE_DIV(1),
		.PROGADDR_RESET('h10000),
		.STACKADDR('h10000)
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
		.mem_rdata   (mem_rdata  ),
		.mem_la_read (mem_la_read ),
		.mem_la_write(mem_la_write),
		.mem_la_addr (mem_la_addr ),
		.mem_la_wdata(mem_la_wdata),
		.mem_la_wstrb(mem_la_wstrb)
	);

	reg [7:0] memory [0:256*1024-1];
	initial $readmemh("dhry.hex", memory);

	assign mem_ready = 1;

	always @(posedge clk) begin
		mem_rdata[ 7: 0] <= mem_la_read ? memory[mem_la_addr + 0] : 'bx;
		mem_rdata[15: 8] <= mem_la_read ? memory[mem_la_addr + 1] : 'bx;
		mem_rdata[23:16] <= mem_la_read ? memory[mem_la_addr + 2] : 'bx;
		mem_rdata[31:24] <= mem_la_read ? memory[mem_la_addr + 3] : 'bx;
		if (mem_la_write) begin
			case (mem_la_addr)
				32'h1000_0000: begin
`ifndef TIMING
					$write("%c", mem_la_wdata);
					$fflush();
`endif
				end
				default: begin
					if (mem_la_wstrb[0]) memory[mem_la_addr + 0] <= mem_la_wdata[ 7: 0];
					if (mem_la_wstrb[1]) memory[mem_la_addr + 1] <= mem_la_wdata[15: 8];
					if (mem_la_wstrb[2]) memory[mem_la_addr + 2] <= mem_la_wdata[23:16];
					if (mem_la_wstrb[3]) memory[mem_la_addr + 3] <= mem_la_wdata[31:24];
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

`ifdef TIMING
	initial begin
		repeat (100000) @(posedge clk);
		$finish;
	end
	always @(posedge clk) begin
		if (uut.dbg_next)
			$display("## %-s %d", uut.dbg_ascii_instr ? uut.dbg_ascii_instr : "pcpi", uut.count_cycle);
	end
`endif
endmodule
