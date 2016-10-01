module testbench (
	input         clk,
	output        trap,

	output        mem_axi_awvalid,
	input         mem_axi_awready,
	output [31:0] mem_axi_awaddr,
	output [ 2:0] mem_axi_awprot,

	output        mem_axi_wvalid,
	input         mem_axi_wready,
	output [31:0] mem_axi_wdata,
	output [ 3:0] mem_axi_wstrb,

	input         mem_axi_bvalid,
	output        mem_axi_bready,

	output        mem_axi_arvalid,
	input         mem_axi_arready,
	output [31:0] mem_axi_araddr,
	output [ 2:0] mem_axi_arprot,

	input         mem_axi_rvalid,
	output        mem_axi_rready,
	input  [31:0] mem_axi_rdata
);
	reg resetn = 0;

	always @(posedge clk)
		resetn <= 1;

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
	) uut (
		.clk             (clk            ),
		.resetn          (resetn         ),
		.trap            (trap           ),
		.mem_axi_awvalid (mem_axi_awvalid),
		.mem_axi_awready (mem_axi_awready),
		.mem_axi_awaddr  (mem_axi_awaddr ),
		.mem_axi_awprot  (mem_axi_awprot ),
		.mem_axi_wvalid  (mem_axi_wvalid ),
		.mem_axi_wready  (mem_axi_wready ),
		.mem_axi_wdata   (mem_axi_wdata  ),
		.mem_axi_wstrb   (mem_axi_wstrb  ),
		.mem_axi_bvalid  (mem_axi_bvalid ),
		.mem_axi_bready  (mem_axi_bready ),
		.mem_axi_arvalid (mem_axi_arvalid),
		.mem_axi_arready (mem_axi_arready),
		.mem_axi_araddr  (mem_axi_araddr ),
		.mem_axi_arprot  (mem_axi_arprot ),
		.mem_axi_rvalid  (mem_axi_rvalid ),
		.mem_axi_rready  (mem_axi_rready ),
		.mem_axi_rdata   (mem_axi_rdata  )
	);

	reg expect_bvalid_aw = 0;
	reg expect_bvalid_w  = 0;
	reg expect_rvalid    = 0;

	reg [3:0] timeout_aw = 0;
	reg [3:0] timeout_w  = 0;
	reg [3:0] timeout_b  = 0;
	reg [3:0] timeout_ar = 0;
	reg [3:0] timeout_r  = 0;
	reg [3:0] timeout_ex = 0;

	always @(posedge clk) begin
		timeout_aw <= !mem_axi_awvalid || mem_axi_awready ? 0 : timeout_aw + 1;
		timeout_w  <= !mem_axi_wvalid  || mem_axi_wready  ? 0 : timeout_w  + 1;
		timeout_b  <= !mem_axi_bvalid  || mem_axi_bready  ? 0 : timeout_b  + 1;
		timeout_ar <= !mem_axi_arvalid || mem_axi_arready ? 0 : timeout_ar + 1;
		timeout_r  <= !mem_axi_rvalid  || mem_axi_rready  ? 0 : timeout_r  + 1;
		timeout_ex <= !{expect_bvalid_aw, expect_bvalid_w, expect_rvalid} ? 0 : timeout_ex + 1;
		restrict(timeout_aw != 15);
		restrict(timeout_w  != 15);
		restrict(timeout_b  != 15);
		restrict(timeout_ar != 15);
		restrict(timeout_r  != 15);
		restrict(timeout_ex != 15);
		restrict(!trap);

	end

	always @(posedge clk) begin
		if (resetn) begin
			if (!$past(resetn)) begin
				assert(!mem_axi_awvalid);
				assert(!mem_axi_wvalid );
				assume(!mem_axi_bvalid );
				assert(!mem_axi_arvalid);
				assume(!mem_axi_rvalid );
			end else begin
				// Only one read/write transaction in flight at each point in time

				if (expect_bvalid_aw) begin
					assert(!mem_axi_awvalid);
				end

				if (expect_bvalid_w) begin
					assert(!mem_axi_wvalid);
				end

				if (expect_rvalid) begin
					assert(!mem_axi_arvalid);
				end

				expect_bvalid_aw = expect_bvalid_aw || (mem_axi_awvalid && mem_axi_awready);
				expect_bvalid_w  = expect_bvalid_w  || (mem_axi_wvalid  && mem_axi_wready );
				expect_rvalid    = expect_rvalid    || (mem_axi_arvalid && mem_axi_arready);

				if (expect_bvalid_aw || expect_bvalid_w) begin
					assert(!expect_rvalid);
				end

				if (expect_rvalid) begin
					assert(!expect_bvalid_aw);
					assert(!expect_bvalid_w);
				end

				if (!expect_bvalid_aw || !expect_bvalid_w) begin
					assume(!mem_axi_bvalid);
				end

				if (!expect_rvalid) begin
					assume(!mem_axi_rvalid);
				end

				if (mem_axi_bvalid && mem_axi_bready) begin
					expect_bvalid_aw = 0;
					expect_bvalid_w = 0;
				end

				if (mem_axi_rvalid && mem_axi_rready) begin
					expect_rvalid = 0;
				end

				// Check AXI Master Streams

				if ($past(mem_axi_awvalid && !mem_axi_awready)) begin
					assert(mem_axi_awvalid);
					assert($stable(mem_axi_awaddr));
					assert($stable(mem_axi_awprot));
				end
				if ($fell(mem_axi_awvalid)) begin
					assert($past(mem_axi_awready));
				end
				if ($fell(mem_axi_awready)) begin
					assume($past(mem_axi_awvalid));
				end

				if ($past(mem_axi_arvalid && !mem_axi_arready)) begin
					assert(mem_axi_arvalid);
					assert($stable(mem_axi_araddr));
					assert($stable(mem_axi_arprot));
				end
				if ($fell(mem_axi_arvalid)) begin
					assert($past(mem_axi_arready));
				end
				if ($fell(mem_axi_arready)) begin
					assume($past(mem_axi_arvalid));
				end

				if ($past(mem_axi_wvalid && !mem_axi_wready)) begin
					assert(mem_axi_wvalid);
					assert($stable(mem_axi_wdata));
					assert($stable(mem_axi_wstrb));
				end
				if ($fell(mem_axi_wvalid)) begin
					assert($past(mem_axi_wready));
				end
				if ($fell(mem_axi_wready)) begin
					assume($past(mem_axi_wvalid));
				end

				// Check AXI Slave Streams

				if ($past(mem_axi_bvalid && !mem_axi_bready)) begin
					assume(mem_axi_bvalid);
				end
				if ($fell(mem_axi_bvalid)) begin
					assume($past(mem_axi_bready));
				end
				if ($fell(mem_axi_bready)) begin
					assert($past(mem_axi_bvalid));
				end

				if ($past(mem_axi_rvalid && !mem_axi_rready)) begin
					assume(mem_axi_rvalid);
					assume($stable(mem_axi_rdata));
				end
				if ($fell(mem_axi_rvalid)) begin
					assume($past(mem_axi_rready));
				end
				if ($fell(mem_axi_rready)) begin
					assert($past(mem_axi_rvalid));
				end
			end
		end
	end
endmodule
