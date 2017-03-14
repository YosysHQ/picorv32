`timescale 1 ns / 1 ps

`ifndef VERILATOR
module testbench #(
	parameter VERBOSE = 0
);
	reg clk = 1;
	reg resetn = 1;
	wire trap;

	always #5 clk = ~clk;

	initial begin
		repeat (100) @(posedge clk);
		resetn <= 0;
	end

	initial begin
		if ($test$plusargs("vcd")) begin
			$dumpfile("testbench_wb.vcd");
			$dumpvars(0, testbench);
		end
		repeat (1000000) @(posedge clk);
		$display("TIMEOUT");
		$finish;
	end

	wire trace_valid;
	wire [35:0] trace_data;
	integer trace_file;

	initial begin
		if ($test$plusargs("trace")) begin
			trace_file = $fopen("testbench.trace", "w");
			repeat (10) @(posedge clk);
			while (!trap) begin
				@(posedge clk);
				if (trace_valid)
					$fwrite(trace_file, "%x\n", trace_data);
			end
			$fclose(trace_file);
			$display("Finished writing testbench.trace.");
		end
	end

	picorv32_wrapper #(
		.VERBOSE (VERBOSE)
	) top (
		.wb_clk(clk),
		.wb_rst(resetn),
		.trap(trap),
		.trace_valid(trace_valid),
		.trace_data(trace_data)
	);
endmodule
`endif

module picorv32_wrapper #(
	parameter BOOTROM_MEMFILE = "",
	parameter BOOTROM_MEMDEPTH = 16384 * 4,
	parameter VERBOSE = 0
) (
	input wb_clk,
	input wb_rst,
	output trap,
	output trace_valid,
	output [35:0] trace_data
);
	wire tests_passed;
	reg [31:0] irq;

	always @* begin
		irq = 0;
		irq[4] = &uut.picorv32_core.count_cycle[12:0];
		irq[5] = &uut.picorv32_core.count_cycle[15:0];
	end

	wire [31:0] wb_m2s_adr;
	wire [31:0] wb_m2s_dat;
	wire [3:0] wb_m2s_sel;
	wire wb_m2s_we;
	wire wb_m2s_cyc;
	wire wb_m2s_stb;
	//wire [2:0] wb_m2s_cti;
	reg [2:0] wb_m2s_cti = 3'b000;
	wire [1:0] wb_m2s_bte;
	wire [31:0] wb_s2m_dat;
	wire wb_s2m_ack;
	wire wb_s2m_err;
	wire wb_s2m_rty;

	wb_ram #(
		.depth (16384 * 4),
		.memfile ("firmware/firmware.hex"),
		.VERBOSE (VERBOSE)
	) ram ( // Wishbone interface
		.wb_clk_i(wb_clk),
		.wb_rst_i(wb_rst),

		.wb_adr_i(wb_m2s_adr),
		.wb_dat_i(wb_m2s_dat),
		.wb_stb_i(wb_m2s_stb),
		.wb_cyc_i(wb_m2s_cyc),
		.wb_dat_o(wb_s2m_dat),
		.wb_ack_o(wb_s2m_ack),
		.wb_sel_i(wb_m2s_sel),
		.wb_cti_i(wb_m2s_cti),
		.wb_bte_i(wb_m2s_bte),
		.wb_we_i(wb_m2s_we),
		.wb_err_o(),

		.tests_passed(tests_passed)
	);

	picorv32_wb #(
`ifndef SYNTH_TEST
`ifdef SP_TEST
		.ENABLE_REGS_DUALPORT(0),
`endif
`ifdef COMPRESSED_ISA
		.COMPRESSED_ISA(1),
`endif
		.ENABLE_MUL(1),
		.ENABLE_DIV(1),
		.ENABLE_IRQ(1),
		.ENABLE_TRACE(1)
`endif
	) uut (
		.trap (trap),
		.irq (irq),
		.trace_valid (trace_valid),
		.trace_data (trace_data),

		.wb_clk_i(wb_clk),
		.wb_rst_i(wb_rst),

		.wbm_adr_o(wb_m2s_adr),
		.wbm_dat_i(wb_s2m_dat),
		.wbm_stb_o(wb_m2s_stb),
		.wbm_ack_i(wb_s2m_ack),
		.wbm_cyc_o(wb_m2s_cyc),
		.wbm_dat_o(wb_m2s_dat),
		.wbm_we_o(wb_m2s_we),
		.wbm_sel_o(wb_m2s_sel)
	);

	integer cycle_counter;
	always @(posedge wb_clk) begin
		cycle_counter <= !wb_rst ? cycle_counter + 1 : 0;
		if (!wb_rst && trap) begin
`ifndef VERILATOR
			repeat (10) @(posedge wb_clk);
`endif
			$display("TRAP after %1d clock cycles", cycle_counter);
			if (tests_passed) begin
				$display("ALL TESTS PASSED.");
				$finish;
			end else begin
				$display("ERROR!");
				if ($test$plusargs("noerror"))
					$finish;
				$stop;
			end
		end
	end
endmodule

module wb_ram #(
	//Wishbone parameters
	parameter dw = 32,
	//Memory parameters
	parameter depth = 256,
	parameter aw = 32,
	parameter memfile = "",
	parameter VERBOSE = 0
) (
	input wb_clk_i,
	input wb_rst_i,

	input [aw-1:0] wb_adr_i,
	input [dw-1:0] wb_dat_i,
	input [3:0] wb_sel_i,
	input wb_we_i,
	input [1:0] wb_bte_i,
	input [2:0] wb_cti_i,
	input wb_cyc_i,
	input wb_stb_i,

	output reg wb_ack_o,
	output wb_err_o,
	output reg [dw-1:0] wb_dat_o,

	output reg tests_passed
);

	localparam CLASSIC_CYCLE = 1'b0;
	localparam BURST_CYCLE   = 1'b1;

	localparam READ  = 1'b0;
	localparam WRITE = 1'b1;

	localparam [2:0]
		CTI_CLASSIC      = 3'b000,
		CTI_CONST_BURST  = 3'b001,
		CTI_INC_BURST    = 3'b010,
		CTI_END_OF_BURST = 3'b111;

	localparam [1:0]
		BTE_LINEAR  = 2'd0,
		BTE_WRAP_4  = 2'd1,
		BTE_WRAP_8  = 2'd2,
		BTE_WRAP_16 = 2'd3;

	function wb_is_last;
		input [2:0] cti;
		begin
			case (cti)
				CTI_CLASSIC      : wb_is_last = 1'b1;
				CTI_CONST_BURST  : wb_is_last = 1'b0;
				CTI_INC_BURST    : wb_is_last = 1'b0;
				CTI_END_OF_BURST : wb_is_last = 1'b1;
				default : $display("%d : Illegal Wishbone B3 cycle type (%b)", $time, cti);
			endcase
		end
	endfunction

	function [31:0] wb_next_adr;
		input [31:0] adr_i;
		input [2:0] cti_i;
		input [2:0] bte_i;
		input integer dw;

		reg [31:0] adr;
		integer shift;
		begin
			shift = $clog2(dw/8);
			adr = adr_i >> shift;
			if (cti_i == CTI_INC_BURST)
				case (bte_i)
				BTE_LINEAR   : adr = adr + 1;
				BTE_WRAP_4   : adr = {adr[31:2], adr[1:0]+2'd1};
				BTE_WRAP_8   : adr = {adr[31:3], adr[2:0]+3'd1};
				BTE_WRAP_16  : adr = {adr[31:4], adr[3:0]+4'd1};
				endcase // case (burst_type_i)

			wb_next_adr = adr << shift;
		end
	endfunction

	reg verbose;
	initial verbose = $test$plusargs("verbose") || VERBOSE;

	initial tests_passed = 0;

	reg [aw-1:0] adr_r;
	wire [aw-1:0] next_adr;
	wire valid = wb_cyc_i & wb_stb_i;
	reg valid_r;
	reg is_last_r;

	always @(posedge wb_clk_i)
		is_last_r <= wb_is_last(wb_cti_i);

	wire new_cycle = (valid & !valid_r) | is_last_r;

	assign next_adr = wb_next_adr(adr_r, wb_cti_i, wb_bte_i, dw);

	wire [aw-1:0] adr = new_cycle ? wb_adr_i : next_adr;

	always @(posedge wb_clk_i) begin
		adr_r <= adr;
		valid_r <= valid;
		// Ack generation
		wb_ack_o <= valid & (!((wb_cti_i == 3'b000) | (wb_cti_i == 3'b111)) | !wb_ack_o);
		if (wb_rst_i)
		begin
			adr_r <= {aw{1'b0}};
			valid_r <= 1'b0;
			wb_ack_o <= 1'b0;
		end
	end

	wire ram_we = wb_we_i & valid & wb_ack_o;

	assign wb_err_o = 1'b0;

	wire [aw-1:0] waddr = adr_r[aw-1:2];
	wire [aw-1:0] raddr = adr[aw-1:2];
	wire [3:0] we = {4{ram_we}} & wb_sel_i;

	wire [$clog2(depth/4)-1:0] raddr2 = raddr[$clog2(depth/4)-1:0];
	wire [$clog2(depth/4)-1:0] waddr2 = waddr[$clog2(depth/4)-1:0];

	reg [31:0] mem [0:depth/4-1] /* verilator public */;

	always @(posedge wb_clk_i) begin
		if (adr_r[aw-1:0] == 32'h1000_0000 && wb_stb_i && !wb_ack_o)
		begin
			$write("%c", wb_dat_i[7:0]);
		end else
		if (adr_r[aw-1:0] == 32'h2000_0000 && wb_stb_i && !wb_ack_o) begin
			if (wb_dat_i[31:0] == 123456789)
				tests_passed = 1;
		end
	end

	always @(posedge wb_clk_i) begin
		if (waddr2 < 64 * 1024 / 4) begin
			if (we[0])
				mem[waddr2][7:0] <= wb_dat_i[7:0];

			if (we[1])
				mem[waddr2][15:8] <= wb_dat_i[15:8];

			if (we[2])
				mem[waddr2][23:16] <= wb_dat_i[23:16];

			if (we[3])
				mem[waddr2][31:24] <= wb_dat_i[31:24];

			if (ram_we)
				if (verbose)
					$display("WR: ADDR=%08x DATA=%08x STRB=%04b",
						adr_r, wb_dat_i, we);
		end

		if (valid & wb_ack_o & !ram_we)
			if (verbose)
				$display("RD: ADDR=%08x DATA=%08x%s", adr_r, mem[raddr2], 0 ? " INSN" : "");

		wb_dat_o <= mem[raddr2];
	end

	initial begin
		if (memfile != "")
			$readmemh(memfile, mem);
	end
endmodule
