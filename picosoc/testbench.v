/*
 *  PicoSoC - A simple example SoC using PicoRV32
 *
 *  Copyright (C) 2017  Clifford Wolf <clifford@clifford.at>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

`timescale 1 ns / 1 ps

module testbench;
	reg clk;
	always #5 clk = (clk === 1'b0);

	reg resetn = 0;

	initial begin
		$dumpfile("testbench.vcd");
		$dumpvars(0, testbench);

		repeat (100) @(posedge clk);
		resetn <= 1;

		repeat (100000) @(posedge clk);

		$display("");
		$display("[TIMEOUT]");
		$stop;
	end

	wire flash_csb;
	wire flash_clk;

	wire flash_io0;
	wire flash_io1;
	wire flash_io2;
	wire flash_io3;

	wire flash_io0_oe;
	wire flash_io1_oe;
	wire flash_io2_oe;
	wire flash_io3_oe;

	wire flash_io0_do;
	wire flash_io1_do;
	wire flash_io2_do;
	wire flash_io3_do;

	wire flash_io0_di = flash_io0;
	wire flash_io1_di = flash_io1;
	wire flash_io2_di = flash_io2;
	wire flash_io3_di = flash_io3;

	assign flash_io0 = flash_io0_oe ? flash_io0_do : 1'bz;
	assign flash_io1 = flash_io1_oe ? flash_io1_do : 1'bz;
	assign flash_io2 = flash_io2_oe ? flash_io2_do : 1'bz;
	assign flash_io3 = flash_io3_oe ? flash_io3_do : 1'bz;

	wire        iomem_valid;
	reg         iomem_ready;
	wire [3:0]  iomem_wstrb;
	wire [31:0] iomem_addr;
	wire [31:0] iomem_wdata;
	reg  [31:0] iomem_rdata;

	reg [31:0] gpio;

	always @(posedge clk) begin
		iomem_ready <= 0;
		if (iomem_valid && !iomem_ready && iomem_addr[31:24] == 8'h 03) begin
			iomem_ready <= 1;
			iomem_rdata <= gpio;
			if (iomem_wstrb[0]) gpio[ 7: 0] <= iomem_wdata[ 7: 0];
			if (iomem_wstrb[1]) gpio[15: 8] <= iomem_wdata[15: 8];
			if (iomem_wstrb[2]) gpio[23:16] <= iomem_wdata[23:16];
			if (iomem_wstrb[3]) gpio[31:24] <= iomem_wdata[31:24];
		end
	end

	always @(gpio) begin
		$write("<GPIO:%02x>", gpio[7:0]);
		if (gpio == 63) begin
			$display("[OK]");
			$finish;
		end
		if (gpio % 8 == 7) begin
			$display("");
		end
	end

	picosoc uut (
		.clk          (clk         ),
		.resetn       (resetn      ),

		.flash_csb    (flash_csb   ),
		.flash_clk    (flash_clk   ),

		.flash_io0_oe (flash_io0_oe),
		.flash_io1_oe (flash_io1_oe),
		.flash_io2_oe (flash_io2_oe),
		.flash_io3_oe (flash_io3_oe),

		.flash_io0_do (flash_io0_do),
		.flash_io1_do (flash_io1_do),
		.flash_io2_do (flash_io2_do),
		.flash_io3_do (flash_io3_do),

		.flash_io0_di (flash_io0_di),
		.flash_io1_di (flash_io1_di),
		.flash_io2_di (flash_io2_di),
		.flash_io3_di (flash_io3_di),

		.iomem_valid  (iomem_valid ),
		.iomem_ready  (iomem_ready ),
		.iomem_wstrb  (iomem_wstrb ),
		.iomem_addr   (iomem_addr  ),
		.iomem_wdata  (iomem_wdata ),
		.iomem_rdata  (iomem_rdata )
	);

	spiflash spiflash (
		.csb(flash_csb),
		.clk(flash_clk),
		.io0(flash_io0),
		.io1(flash_io1),
		.io2(flash_io2),
		.io3(flash_io3)
	);
endmodule
