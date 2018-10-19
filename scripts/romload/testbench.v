`timescale 1 ns / 1 ps
`undef VERBOSE_MEM
//`undef WRITE_VCD
`undef MEM8BIT

// define the size of our ROM
// simulates ROM by suppressing writes below this address
`define ROM_SIZE 32'h0001_00FF

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
	reg mem_ready;
	wire [31:0] mem_addr;
	wire [31:0] mem_wdata;
	wire [3:0] mem_wstrb;
	reg  [31:0] mem_rdata;

`include "firmware_dbg.v"

	picorv32 #(
		.COMPRESSED_ISA(1),
		.PROGADDR_RESET(32'h100)
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

	localparam MEM_SIZE = 4*1024*1024;
`ifdef MEM8BIT
	reg [7:0] memory [0:MEM_SIZE-1];
	initial 
		$readmemh("firmware.hex", memory);
	end
`else
	reg [31:0] memory [0:MEM_SIZE/4-1];
	integer x;

	// simulate hardware assist of clearing RAM and copying ROM data into
	// memory
	initial
	begin
		// clear memory
		for (x=0; x<MEM_SIZE/4; x=x+1) memory[x] = 0;
		// load rom contents
		$readmemh("firmware32.hex", memory);
		// copy .data section
		for (x=0; x<(`C_SYM__BSS_START - `C_SYM___GLOBAL_POINTER); x=x+4)
			memory[(`C_SYM___GLOBAL_POINTER+x)/4] = memory[(`C_SYM__DATA_LMA+x)/4];
	end
`endif

	always @(posedge clk) begin
		mem_ready <= 0;
		if (mem_valid && !mem_ready) begin
			mem_ready <= 1;
			mem_rdata <= 'bx;
			case (1)
				mem_addr < MEM_SIZE: begin
`ifdef MEM8BIT
					if (|mem_wstrb) begin
						if (mem_wstrb[0]) memory[mem_addr + 0] <= mem_wdata[ 7: 0];
						if (mem_wstrb[1]) memory[mem_addr + 1] <= mem_wdata[15: 8];
						if (mem_wstrb[2]) memory[mem_addr + 2] <= mem_wdata[23:16];
						if (mem_wstrb[3]) memory[mem_addr + 3] <= mem_wdata[31:24];
					end else begin
						mem_rdata <= {memory[mem_addr+3], memory[mem_addr+2], memory[mem_addr+1], memory[mem_addr]};
					end
`else
					if ((|mem_wstrb) && (mem_addr >= `ROM_SIZE)) begin
						if (mem_wstrb[0]) memory[mem_addr >> 2][ 7: 0] <= mem_wdata[ 7: 0];
						if (mem_wstrb[1]) memory[mem_addr >> 2][15: 8] <= mem_wdata[15: 8];
						if (mem_wstrb[2]) memory[mem_addr >> 2][23:16] <= mem_wdata[23:16];
						if (mem_wstrb[3]) memory[mem_addr >> 2][31:24] <= mem_wdata[31:24];
					end else begin
						mem_rdata <= memory[mem_addr >> 2];
					end
`endif
				end
				mem_addr == 32'h 1000_0000: begin
					$write("%c", mem_wdata[7:0]);
				end
			endcase
		end
		if (mem_valid && mem_ready) begin
`ifdef FIRMWARE_DEBUG_ADDR
			firmware_dbg(mem_addr);
`endif
			if ((mem_wstrb == 4'h0) && (mem_rdata === 32'bx)) $display("READ FROM UNITIALIZED ADDR=%x", mem_addr);
`ifdef VERBOSE_MEM
			if (|mem_wstrb)
				$display("WR: ADDR=%x DATA=%x MASK=%b", mem_addr, mem_wdata, mem_wstrb);
			else
				$display("RD: ADDR=%x DATA=%x%s", mem_addr, mem_rdata, mem_instr ? " INSN" : "");
`endif
			if (^mem_addr === 1'bx ||
					(mem_wstrb[0] && ^mem_wdata[ 7: 0] == 1'bx) ||
					(mem_wstrb[1] && ^mem_wdata[15: 8] == 1'bx) ||
					(mem_wstrb[2] && ^mem_wdata[23:16] == 1'bx) ||
					(mem_wstrb[3] && ^mem_wdata[31:24] == 1'bx)) begin
				$display("CRITICAL UNDEF MEM TRANSACTION");
				$finish;
			end
		end
	end

`ifdef WRITE_VCD
	initial begin
		$dumpfile("testbench.vcd");
		$dumpvars(0, testbench);
	end
`endif

	always @(posedge clk) begin
		if (resetn && trap) begin
			repeat (10) @(posedge clk);
			$display("TRAP");
			$finish;
		end
	end
endmodule
