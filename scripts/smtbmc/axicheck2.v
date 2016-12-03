module testbench (
	input         clk,
	input         resetn,
	output        trap_0,
	output        trap_1,

	output        mem_axi_awvalid_0,
	input         mem_axi_awready_0,
	output [31:0] mem_axi_awaddr_0,
	output [ 2:0] mem_axi_awprot_0,

	output        mem_axi_awvalid_1,
	input         mem_axi_awready_1,
	output [31:0] mem_axi_awaddr_1,
	output [ 2:0] mem_axi_awprot_1,

	output        mem_axi_wvalid_0,
	input         mem_axi_wready_0,
	output [31:0] mem_axi_wdata_0,
	output [ 3:0] mem_axi_wstrb_0,

	output        mem_axi_wvalid_1,
	input         mem_axi_wready_1,
	output [31:0] mem_axi_wdata_1,
	output [ 3:0] mem_axi_wstrb_1,

	input         mem_axi_bvalid,
	output        mem_axi_bready_0,
	output        mem_axi_bready_1,

	output        mem_axi_arvalid_0,
	input         mem_axi_arready_0,
	output [31:0] mem_axi_araddr_0,
	output [ 2:0] mem_axi_arprot_0,

	output        mem_axi_arvalid_1,
	input         mem_axi_arready_1,
	output [31:0] mem_axi_araddr_1,
	output [ 2:0] mem_axi_arprot_1,

	input         mem_axi_rvalid,
	output        mem_axi_rready_0,
	output        mem_axi_rready_1,
	input  [31:0] mem_axi_rdata
);
	picorv32_axi #(
		.ENABLE_COUNTERS(1),
		.ENABLE_COUNTERS64(1),
		.ENABLE_REGS_16_31(1),
		.ENABLE_REGS_DUALPORT(1),
		.BARREL_SHIFTER(1),
		.TWO_CYCLE_COMPARE(0),
		.TWO_CYCLE_ALU(0),
		.COMPRESSED_ISA(0),
		.CATCH_MISALIGN(1),
		.CATCH_ILLINSN(1)
	) uut_0 (
		.clk             (clk              ),
		.resetn          (resetn           ),
		.trap            (trap_0           ),
		.mem_axi_awvalid (mem_axi_awvalid_0),
		.mem_axi_awready (mem_axi_awready_0),
		.mem_axi_awaddr  (mem_axi_awaddr_0 ),
		.mem_axi_awprot  (mem_axi_awprot_0 ),
		.mem_axi_wvalid  (mem_axi_wvalid_0 ),
		.mem_axi_wready  (mem_axi_wready_0 ),
		.mem_axi_wdata   (mem_axi_wdata_0  ),
		.mem_axi_wstrb   (mem_axi_wstrb_0  ),
		.mem_axi_bvalid  (mem_axi_bvalid   ),
		.mem_axi_bready  (mem_axi_bready_0 ),
		.mem_axi_arvalid (mem_axi_arvalid_0),
		.mem_axi_arready (mem_axi_arready_0),
		.mem_axi_araddr  (mem_axi_araddr_0 ),
		.mem_axi_arprot  (mem_axi_arprot_0 ),
		.mem_axi_rvalid  (mem_axi_rvalid   ),
		.mem_axi_rready  (mem_axi_rready_0 ),
		.mem_axi_rdata   (mem_axi_rdata    )
	);

	picorv32_axi #(
		.ENABLE_COUNTERS(1),
		.ENABLE_COUNTERS64(1),
		.ENABLE_REGS_16_31(1),
		.ENABLE_REGS_DUALPORT(1),
		.BARREL_SHIFTER(1),
		.TWO_CYCLE_COMPARE(0),
		.TWO_CYCLE_ALU(0),
		.COMPRESSED_ISA(0),
		.CATCH_MISALIGN(1),
		.CATCH_ILLINSN(1)
	) uut_1 (
		.clk             (clk              ),
		.resetn          (resetn           ),
		.trap            (trap_1           ),
		.mem_axi_awvalid (mem_axi_awvalid_1),
		.mem_axi_awready (mem_axi_awready_1),
		.mem_axi_awaddr  (mem_axi_awaddr_1 ),
		.mem_axi_awprot  (mem_axi_awprot_1 ),
		.mem_axi_wvalid  (mem_axi_wvalid_1 ),
		.mem_axi_wready  (mem_axi_wready_1 ),
		.mem_axi_wdata   (mem_axi_wdata_1  ),
		.mem_axi_wstrb   (mem_axi_wstrb_1  ),
		.mem_axi_bvalid  (mem_axi_bvalid   ),
		.mem_axi_bready  (mem_axi_bready_1 ),
		.mem_axi_arvalid (mem_axi_arvalid_1),
		.mem_axi_arready (mem_axi_arready_1),
		.mem_axi_araddr  (mem_axi_araddr_1 ),
		.mem_axi_arprot  (mem_axi_arprot_1 ),
		.mem_axi_rvalid  (mem_axi_rvalid   ),
		.mem_axi_rready  (mem_axi_rready_1 ),
		.mem_axi_rdata   (mem_axi_rdata    )
	);

	always @(posedge clk) begin
		if (resetn && $past(resetn)) begin
			assert(trap_0            == trap_1           );
			assert(mem_axi_awvalid_0 == mem_axi_awvalid_1);
			assert(mem_axi_awaddr_0  == mem_axi_awaddr_1 );
			assert(mem_axi_awprot_0  == mem_axi_awprot_1 );
			assert(mem_axi_wvalid_0  == mem_axi_wvalid_1 );
			assert(mem_axi_wdata_0   == mem_axi_wdata_1  );
			assert(mem_axi_wstrb_0   == mem_axi_wstrb_1  );
			assert(mem_axi_bready_0  == mem_axi_bready_1 );
			assert(mem_axi_arvalid_0 == mem_axi_arvalid_1);
			assert(mem_axi_araddr_0  == mem_axi_araddr_1 );
			assert(mem_axi_arprot_0  == mem_axi_arprot_1 );
			assert(mem_axi_rready_0  == mem_axi_rready_1 );

			if (mem_axi_awvalid_0) assume(mem_axi_awready_0 == mem_axi_awready_1);
			if (mem_axi_wvalid_0 ) assume(mem_axi_wready_0  == mem_axi_wready_1 );
			if (mem_axi_arvalid_0) assume(mem_axi_arready_0 == mem_axi_arready_1);

			if ($fell(mem_axi_awready_0)) assume($past(mem_axi_awvalid_0));
			if ($fell(mem_axi_wready_0 )) assume($past(mem_axi_wvalid_0 ));
			if ($fell(mem_axi_arready_0)) assume($past(mem_axi_arvalid_0));

			if ($fell(mem_axi_awready_1)) assume($past(mem_axi_awvalid_1));
			if ($fell(mem_axi_wready_1 )) assume($past(mem_axi_wvalid_1 ));
			if ($fell(mem_axi_arready_1)) assume($past(mem_axi_arvalid_1));

			if ($fell(mem_axi_bvalid)) assume($past(mem_axi_bready_0));
			if ($fell(mem_axi_rvalid)) assume($past(mem_axi_rready_0));

			if (mem_axi_rvalid && $past(mem_axi_rvalid)) assume($stable(mem_axi_rdata));
		end
	end
endmodule
