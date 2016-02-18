// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

module picorv32_wrapper #(
	parameter AXI_TEST = 0,
	parameter VERBOSE = 0
) (
	input clk,
	input resetn
);

	wire       trap;
	reg [31:0] irq;

	always @* begin
		irq = 0;
		irq[4] = &uut.picorv32_core.count_cycle[12:0];
		irq[5] = &uut.picorv32_core.count_cycle[15:0];
	end

	wire        mem_axi_awvalid;
	wire        mem_axi_awready;
	wire [31:0] mem_axi_awaddr;
	wire [ 2:0] mem_axi_awprot;

	wire        mem_axi_wvalid;
	wire        mem_axi_wready;
	wire [31:0] mem_axi_wdata;
	wire [ 3:0] mem_axi_wstrb;

	wire        mem_axi_bvalid;
	wire        mem_axi_bready;

	wire        mem_axi_arvalid;
	wire        mem_axi_arready;
	wire [31:0] mem_axi_araddr;
	wire [ 2:0] mem_axi_arprot;

	wire        mem_axi_rvalid;
	wire        mem_axi_rready;
	wire [31:0] mem_axi_rdata;

	axi4_memory #(
		.AXI_TEST (AXI_TEST),
		.VERBOSE  (VERBOSE)
	) mem (
		.clk             (clk             ),
		.mem_axi_awvalid (mem_axi_awvalid ),
		.mem_axi_awready (mem_axi_awready ),
		.mem_axi_awaddr  (mem_axi_awaddr  ),
		.mem_axi_awprot  (mem_axi_awprot  ),

		.mem_axi_wvalid  (mem_axi_wvalid  ),
		.mem_axi_wready  (mem_axi_wready  ),
		.mem_axi_wdata   (mem_axi_wdata   ),
		.mem_axi_wstrb   (mem_axi_wstrb   ),

		.mem_axi_bvalid  (mem_axi_bvalid  ),
		.mem_axi_bready  (mem_axi_bready  ),

		.mem_axi_arvalid (mem_axi_arvalid ),
		.mem_axi_arready (mem_axi_arready ),
		.mem_axi_araddr  (mem_axi_araddr  ),
		.mem_axi_arprot  (mem_axi_arprot  ),

		.mem_axi_rvalid  (mem_axi_rvalid  ),
		.mem_axi_rready  (mem_axi_rready  ),
		.mem_axi_rdata   (mem_axi_rdata   )
	);

	picorv32_axi #(
`ifdef SP_TEST
		.ENABLE_REGS_DUALPORT(0),
`endif
		.ENABLE_MUL(1),
		.ENABLE_IRQ(1)
	) uut (
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
		.mem_axi_rdata  (mem_axi_rdata  ),
		.irq            (irq            )
	);

	reg [1023:0] firmware_file;
	initial begin
		if(!$value$plusargs("firmware=%s", firmware_file))
			firmware_file = "firmware/firmware.hex";
		$readmemh(firmware_file, mem.memory);
	end

	integer cycle_counter;
	always @(posedge clk) begin
		cycle_counter <= resetn ? cycle_counter + 1 : 0;
		if (resetn && trap) begin
`ifndef VERILATOR
			repeat (10) @(posedge clk);
`endif
			$display("TRAP after %1d clock cycles", cycle_counter);
			$finish;
		end
	end
endmodule
