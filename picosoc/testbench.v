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

module testbench;
	reg clk = 1;
	always #5 clk = ~clk;

	initial begin
		$dumpfile("testbench.vcd");
		$dumpvars(0, testbench);
		repeat (100000) @(posedge clk);
		$display("");
		$display("[TIMEOUT]");
		$stop;
	end

	wire [31:0] gpio_i = 0;
	wire [31:0] gpio_o;

	wire flash_csb;
	wire flash_clk;
	wire flash_io0;
	wire flash_io1;
	wire flash_io2;
	wire flash_io3;

	always @(gpio_o) begin
		$write("<GPIO:%02x>", gpio_o[7:0]);
		if (gpio_o == 63) begin
			$display("[OK]");
			$finish;
		end
		if (gpio_o % 8 == 7) begin
			$display("");
		end
	end

	picosoc uut (
		.clk      (clk      ),
		.gpio_i   (gpio_i   ),
		.gpio_o   (gpio_o   ),
		.flash_csb(flash_csb),
		.flash_clk(flash_clk),
		.flash_io0(flash_io0),
		.flash_io1(flash_io1),
		.flash_io2(flash_io2),
		.flash_io3(flash_io3)
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
