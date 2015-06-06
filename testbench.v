`timescale 1 ns / 1 ps
// `define VERBOSE
// `define RANDOM_AXI_DELAYS

module testbench;

	reg clk = 1;
	reg resetn = 0;
	wire trap;

	always #5 clk = ~clk;

	initial begin
		repeat (100) @(posedge clk);
		resetn <= 1;
	end

	wire        mem_axi_awvalid;
	reg         mem_axi_awready = 0;
	wire [31:0] mem_axi_awaddr;
	wire [ 2:0] mem_axi_awprot;

	wire        mem_axi_wvalid;
	reg         mem_axi_wready = 0;
	wire [31:0] mem_axi_wdata;
	wire [ 3:0] mem_axi_wstrb;

	reg  mem_axi_bvalid = 0;
	wire mem_axi_bready;

	wire        mem_axi_arvalid;
	reg         mem_axi_arready = 0;
	wire [31:0] mem_axi_araddr;
	wire [ 2:0] mem_axi_arprot;

	reg         mem_axi_rvalid = 0;
	wire        mem_axi_rready;
	reg  [31:0] mem_axi_rdata;

	picorv32_axi uut (
		.clk            (clk            ),
		.resetn         (resetn         ),
		.trap           (trap           ),
		.mem_axi_awvalid(mem_axi_awvalid),
		.mem_axi_awready(mem_axi_awready),
		.mem_axi_awaddr (mem_axi_awaddr ),
		.mem_axi_awprot (mem_axi_awprot ),
		.mem_axi_wvalid (mem_axi_wvalid ),
		.mem_axi_wready (mem_axi_wready ),
		.mem_axi_wdata  (mem_axi_wdata  ),
		.mem_axi_wstrb  (mem_axi_wstrb  ),
		.mem_axi_bvalid (mem_axi_bvalid ),
		.mem_axi_bready (mem_axi_bready ),
		.mem_axi_arvalid(mem_axi_arvalid),
		.mem_axi_arready(mem_axi_arready),
		.mem_axi_araddr (mem_axi_araddr ),
		.mem_axi_arprot (mem_axi_arprot ),
		.mem_axi_rvalid (mem_axi_rvalid ),
		.mem_axi_rready (mem_axi_rready ),
		.mem_axi_rdata  (mem_axi_rdata  )
	);

	reg [31:0] memory [0:64*1024/4-1];
	initial $readmemh("firmware/firmware.hex", memory);

	reg [63:0] xorshift64_state = 64'd88172645463325252;

	task xorshift64_next;
		begin
			// see page 4 of Marsaglia, George (July 2003). "Xorshift RNGs". Journal of Statistical Software 8 (14).
			xorshift64_state = xorshift64_state ^ (xorshift64_state << 13);
			xorshift64_state = xorshift64_state ^ (xorshift64_state >>  7);
			xorshift64_state = xorshift64_state ^ (xorshift64_state << 17);
		end
	endtask

	reg delay_axi_transaction = 0;

`ifdef RANDOM_AXI_DELAYS
	always @(posedge clk) begin
		xorshift64_next;
		delay_axi_transaction <= xorshift64_state[0];
	end
`endif

	always @(posedge clk) begin
		mem_axi_awready <= 0;
		mem_axi_wready <= 0;
		mem_axi_arready <= 0;

		if (!mem_axi_bvalid || mem_axi_bready) begin
			mem_axi_bvalid <= 0;
			if (mem_axi_awvalid && mem_axi_wvalid && !mem_axi_awready && !mem_axi_wready && !delay_axi_transaction) begin
`ifdef VERBOSE
				$display("WR: ADDR=%08x DATA=%08x STRB=%04b", mem_axi_awaddr, mem_axi_wdata, mem_axi_wstrb);
`endif
				if (mem_axi_awaddr < 64*1024) begin
					if (mem_axi_wstrb[0]) memory[mem_axi_awaddr >> 2][ 7: 0] <= mem_axi_wdata[ 7: 0];
					if (mem_axi_wstrb[1]) memory[mem_axi_awaddr >> 2][15: 8] <= mem_axi_wdata[15: 8];
					if (mem_axi_wstrb[2]) memory[mem_axi_awaddr >> 2][23:16] <= mem_axi_wdata[23:16];
					if (mem_axi_wstrb[3]) memory[mem_axi_awaddr >> 2][31:24] <= mem_axi_wdata[31:24];
				end
				if (mem_axi_awaddr == 32'h1000_0000) begin
`ifdef VERBOSE
					if (32 <= mem_axi_wdata && mem_axi_wdata < 128)
						$display("OUT: '%c'", mem_axi_wdata);
					else
						$display("OUT: %3d", mem_axi_wdata);
`else
					$write("%c", mem_axi_wdata);
					$fflush();
`endif
				end
				mem_axi_awready <= 1;
				mem_axi_wready <= 1;
				mem_axi_bvalid <= 1;
			end
		end

		if (!mem_axi_rvalid || mem_axi_rready) begin
			mem_axi_rvalid <= 0;
			if (mem_axi_arvalid && !mem_axi_arready && !delay_axi_transaction) begin
`ifdef VERBOSE
				$display("RD: ADDR=%08x DATA=%08x", mem_axi_araddr, memory[mem_axi_araddr >> 2]);
`endif
				mem_axi_arready <= 1;
				mem_axi_rdata <= memory[mem_axi_araddr >> 2];
				mem_axi_rvalid <= 1;
			end
		end
	end

	initial begin
		$dumpfile("testbench.vcd");
		$dumpvars(0, testbench);
		repeat (1000000) @(posedge clk);
		$display("TIMEOUT");
		$finish;
	end

	always @(posedge clk) begin
		if (resetn && trap) begin
			repeat (10) @(posedge clk);
			$display("TRAP");
			$finish;
		end
	end
endmodule
