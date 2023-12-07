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
			$dumpfile("testbench.vcd");
			$dumpvars(0, testbench);
		end
		repeat (100000) @(posedge clk);
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
	parameter VERBOSE = 0
) (
	input wb_clk,
	input wb_rst,
	output trap,
	output trace_valid,
	output [35:0] trace_data
);
	wire tests_passed;
	reg [31:0] irq = 0;
	wire mem_instr;

	reg [15:0] count_cycle = 0;
	always @(posedge wb_clk) count_cycle <= !wb_rst ? count_cycle + 1 : 0;

	always @* begin
		irq = 0;
		irq[4] = &count_cycle[12:0];
		irq[5] = &count_cycle[15:0];
	end

	wire [31:0] wb_m2s_adr;
	wire [31:0] wb_m2s_dat;
	wire [3:0] wb_m2s_sel;
	wire wb_m2s_we;
	wire wb_m2s_cyc;
	wire wb_m2s_stb;
	reg [31:0] wb_s2m_dat;
	reg wb_s2m_ack;

	localparam INNER_ADDR_BASE = 32'h0000_0000;
	localparam INNER_ADDR_WIDTH = 30;
	localparam BRIDGE_ADDR_BASE = 32'h4000_0000;
	localparam BRIDGE_ADDR_WIDTH = 12;

	reg         bridge_wb_stb;
	wire [31:0] bridge_wb_dat_o;
	wire        bridge_wb_ack_o;


	reg         ram_wb_stb;
	wire [31:0] ram_wb_dat_o;
	wire        ram_wb_act_o;

	always @(*) begin
		if (((wb_m2s_adr ^ INNER_ADDR_BASE) >> INNER_ADDR_WIDTH) == 32'd0) begin
			bridge_wb_stb = 1'b0;
			ram_wb_stb    = wb_m2s_stb;
			wb_s2m_dat    = ram_wb_dat_o;
			wb_s2m_ack    = ram_wb_act_o;
		end else if (((wb_m2s_adr ^ BRIDGE_ADDR_BASE) >> BRIDGE_ADDR_WIDTH) == 32'd0) begin
			ram_wb_stb    = 1'b0;
			bridge_wb_stb = wb_m2s_stb;
			wb_s2m_dat    = bridge_wb_dat_o;
			wb_s2m_ack    = bridge_wb_ack_o;
		end
	end

	wire                    pclk;
	wire                    prestn;
	// APB interface 
	wire [BRIDGE_ADDR_WIDTH-1:0]   paddr;
	wire                    psel;
	wire                    penable;
	wire                    pwrite;
	wire [31:0]             pwdata;
	wire                    pready;
	wire [31:0]             prdata;
	wire                    pslverr;

	wishbone2apb #(
		.ADDR_WIDTH(BRIDGE_ADDR_WIDTH)
	) bridge (
		.wb_clk_i(wb_clk),
		.wb_rst_i(wb_rst),

		.wb_adr_i(wb_m2s_adr),
		.wb_dat_i(wb_m2s_dat),
		.wb_stb_i(bridge_wb_stb),
		.wb_cyc_i(wb_m2s_cyc),
		.wb_dat_o(bridge_wb_dat_o),
		.wb_ack_o(bridge_wb_ack_o),
		.wb_sel_i(wb_m2s_sel),
		.wb_we_i(wb_m2s_we),
		.pclk(pclk),
		.prestn(prestn),
		// APB interface 
		.paddr(paddr),
		.psel(psel),
		.penable(penable),
		.pwrite(pwrite),
		.pwdata(pwdata),
		.pready(pready),
		.prdata(prdata),
		.pslverr(pslverr)
	);

	regfile regcfg(
		.PCLK(pclk),
		.PRESETn(prestn),
		.PSEL(psel),
		.PENABLE(penable),
		.PADDR(paddr),
		.PWRITE(pwrite),
		.PWDATA(pwdata),
		.PRDATA(prdata),
		.PREADY(pready),
		.PSLVERR(pslverr)
	);


	wb_ram #(
		.depth (128*1024),
		.VERBOSE (VERBOSE)
	) ram ( // Wishbone interface
		.wb_clk_i(wb_clk),
		.wb_rst_i(wb_rst),

		.wb_adr_i(wb_m2s_adr),
		.wb_dat_i(wb_m2s_dat),
		.wb_stb_i(ram_wb_stb),
		.wb_cyc_i(wb_m2s_cyc),
		.wb_dat_o(ram_wb_dat_o),
		.wb_ack_o(ram_wb_act_o),
		.wb_sel_i(wb_m2s_sel),
		.wb_we_i(wb_m2s_we),

		.mem_instr(mem_instr),
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
		.mem_instr(mem_instr),

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

	reg [1023:0] firmware_file;
	initial begin
		if (!$value$plusargs("firmware=%s", firmware_file))
			firmware_file = "firmware/firmware.hex";
		$readmemh(firmware_file, ram.mem);
	end

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

/* ISC License
 *
 * Verilog on-chip RAM with Wishbone interface
 *
 * Copyright (C) 2014, 2016 Olof Kindgren <olof.kindgren@gmail.com>
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

module wb_ram #(
	parameter depth = 256,
	parameter memfile = "",
	parameter VERBOSE = 0
) (
	input wb_clk_i,
	input wb_rst_i,

	input [31:0] wb_adr_i,
	input [31:0] wb_dat_i,
	input [3:0] wb_sel_i,
	input wb_we_i,
	input wb_cyc_i,
	input wb_stb_i,

	output reg wb_ack_o,
	output reg [31:0] wb_dat_o,

	input mem_instr,
	output reg tests_passed
);

	reg verbose;
	initial verbose = $test$plusargs("verbose") || VERBOSE;

	initial tests_passed = 0;

	reg [31:0] adr_r;
	wire valid = wb_cyc_i & wb_stb_i;

	always @(posedge wb_clk_i) begin
		adr_r <= wb_adr_i;
		// Ack generation
		wb_ack_o <= valid & !wb_ack_o;
		if (wb_rst_i)
		begin
			adr_r <= {32{1'b0}};
			wb_ack_o <= 1'b0;
		end
	end

	wire ram_we = wb_we_i & valid & wb_ack_o;

	wire [31:0] waddr = adr_r[31:2];
	wire [31:0] raddr = wb_adr_i[31:2];
	wire [3:0] we = {4{ram_we}} & wb_sel_i;

	wire [$clog2(depth/4)-1:0] raddr2 = raddr[$clog2(depth/4)-1:0];
	wire [$clog2(depth/4)-1:0] waddr2 = waddr[$clog2(depth/4)-1:0];

	reg [31:0] mem [0:depth/4-1] /* verilator public */;

	always @(posedge wb_clk_i) begin
		if (ram_we) begin
			if (verbose)
				$display("WR: ADDR=%08x DATA=%08x STRB=%04b",
					adr_r, wb_dat_i, we);

			if (adr_r[31:0] == 32'h1000_0000)
				if (verbose) begin
					if (32 <= wb_dat_i[7:0] && wb_dat_i[7:0] < 128)
						$display("OUT: '%c'", wb_dat_i[7:0]);
					else
						$display("OUT: %3d", wb_dat_i[7:0]);
				end else begin
					$write("%c", wb_dat_i[7:0]);
`ifndef VERILATOR
					$fflush();
`endif
				end
			else
			if (adr_r[31:0] == 32'h2000_0000)
				if (wb_dat_i[31:0] == 123456789)
					tests_passed = 1;
		end
	end

	always @(posedge wb_clk_i) begin
		if (waddr2 < 128 * 1024 / 4) begin
			if (we[0])
				mem[waddr2][7:0] <= wb_dat_i[7:0];

			if (we[1])
				mem[waddr2][15:8] <= wb_dat_i[15:8];

			if (we[2])
				mem[waddr2][23:16] <= wb_dat_i[23:16];

			if (we[3])
				mem[waddr2][31:24] <= wb_dat_i[31:24];

		end

		if (valid & wb_ack_o & !ram_we)
			if (verbose)
				$display("RD: ADDR=%08x DATA=%08x%s", adr_r, mem[raddr2], mem_instr ? " INSN" : "");

		wb_dat_o <= mem[raddr2];
	end

	initial begin
		if (memfile != "")
			$readmemh(memfile, mem);
	end
endmodule


module wishbone2apb #(
    parameter ADDR_WIDTH = 10
) (
    // Wishbone clock
    input  wire wb_clk_i,
	input  wire wb_rst_i,
    // Wishbone interface
	input  wire [ADDR_WIDTH-1:0] wb_adr_i,
	input  wire [31:0] wb_dat_i,
	input  wire [3:0] wb_sel_i,
	input  wire wb_we_i,
	input  wire wb_cyc_i,
	input  wire wb_stb_i,
	output wire wb_ack_o,
	output wire [31:0] wb_dat_o,

    // APB clock
    output wire                    pclk,
    output wire                    prestn,
    // APB interface 
    output wire [ADDR_WIDTH-1:0]   paddr,
    output wire                    psel,
    output wire                    penable,
    output wire                    pwrite,
    output wire [31:0]             pwdata,
    input wire                     pready,
    input wire [31:0]              prdata,
    input wire                     pslverr
);


reg                  wb_stb_d;
reg [ 3:0]           wb_sel_d;
reg [ADDR_WIDTH-1:0] wb_adr_d;
reg [31:0]           wb_dat_d;
reg                  wb_we_d;

always @(posedge wb_clk_i or posedge wb_rst_i) begin
    if (wb_rst_i) begin
		wb_stb_d <= 1'b0;
        wb_sel_d <= 4'b0;
        wb_adr_d <= {32{1'd0}};
        wb_dat_d <= 32'd0;
        wb_we_d  <= 1'b0;
    end else begin
        if (wb_stb_i & (wb_stb_d ? wb_ack_o : 1'b1)) begin
            wb_stb_d <= 1'b1;
            wb_sel_d <= wb_sel_i;
            wb_adr_d <= wb_adr_i;
            wb_dat_d <= wb_dat_i;
            wb_we_d  <= wb_we_i;
        end else if (wb_ack_o | (!psel)) begin
            wb_stb_d <= 1'b0;
            wb_sel_d <= 4'b0;
            wb_adr_d <= {32{1'd0}};
            wb_dat_d <= 32'd0;
            wb_we_d  <= 1'b0;
        end
    end
end

reg wb_ack_d;
always @(posedge wb_clk_i or posedge wb_rst_i) begin
    if (wb_rst_i) begin
        wb_ack_d <= 1'b0;
    end else begin
        wb_ack_d <= wb_ack_o;
    end
end


assign pclk = wb_clk_i;
assign prestn = !wb_rst_i;
assign psel = wb_cyc_i & (wb_stb_i | wb_stb_d);
assign penable = wb_cyc_i & wb_stb_d & (!wb_ack_d);

assign paddr = wb_stb_d ? wb_adr_d : wb_adr_i;
assign pwdata = wb_stb_d ? wb_dat_d : wb_dat_i;
assign pwrite = wb_stb_d ? wb_we_d : wb_we_i;

assign wb_ack_o = penable & pready;
assign wb_dat_o = prdata;

always @(wb_clk_i) begin
    if (pslverr) begin
        $display("Wishbone to APB: slave error! addr: 0x%08x write: %d wdata: 0x%08x rdata: 0x%08x", paddr, pwrite, pwdata, prdata);
        $finish;
    end
end
    
endmodule

module regfile #(
    parameter ADDR_WIDTH = 12
)
  (
   input wire        PRESETn,
   input wire        PCLK,
   input wire        PSEL,
   input wire        PENABLE,
   input wire [ADDR_WIDTH-1:0] PADDR,
   input wire        PWRITE,
   input wire [31:0] PWDATA,
   output reg [31:0] PRDATA,
   output wire       PREADY,
   output reg        PSLVERR,

   output reg [31:0] config_reg0,
   output reg [31:0] config_reg1
   );
   reg               rready;

   //READ
   always @(posedge PCLK)
     case(PADDR[ADDR_WIDTH-1:2]) 
        0: PRDATA <= config_reg0;
        1: PRDATA <= config_reg1;
        default: PRDATA <= 32'hDEADBEEF;
     endcase // case (PADDR)


   assign PREADY = PWRITE ? PENABLE : rready;
   
   always @(posedge PCLK or negedge PRESETn) begin
      if(~PRESETn) begin
         rready <= 0;
      end
      else begin
         rready <= 0;
         if(~PWRITE & PSEL & ~rready)
           rready <= 1'b1;
      end
   end

   always @(posedge PCLK or negedge PRESETn)
     if(~PRESETn) begin
        PSLVERR <= 1'b0;
        config_reg0 <= 32'habcd1234;
        config_reg1 <= 32'hdc72ef98;
     end
     else begin
        PSLVERR <= 1'b0;
        if(PSEL & PENABLE & PWRITE)
          case(PADDR[ADDR_WIDTH-1:2]) 
            0: config_reg0 <= PWDATA;
            1: config_reg1 <= PWDATA;
          endcase // case (PADDR)
     end // else: !if(~PRESETn)
 
endmodule
