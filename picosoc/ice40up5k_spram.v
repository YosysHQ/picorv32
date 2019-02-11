
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

module ice40up5k_spram #(
	// We current always use the whole SPRAM (128 kB)
	parameter integer WORDS = 32768
) (
	input clk,
	input [3:0] wen,
	input [21:0] addr,
	input [31:0] wdata,
	output [31:0] rdata
);

	wire cs_0, cs_1;
	wire [31:0] rdata_0, rdata_1;

	assign cs_0 = !addr[14];
	assign cs_1 = addr[14];
	assign rdata = addr[14] ? rdata_1 : rdata_0;

	SB_SPRAM256KA ram00 (
		.ADDRESS(addr[13:0]),
		.DATAIN(wdata[15:0]),
		.MASKWREN({wen[1], wen[1], wen[0], wen[0]}),
		.WREN(wen[1]|wen[0]),
		.CHIPSELECT(cs_0),
		.CLOCK(clk),
		.STANDBY(1'b0),
		.SLEEP(1'b0),
		.POWEROFF(1'b1),
		.DATAOUT(rdata_0[15:0])
	);

	SB_SPRAM256KA ram01 (
		.ADDRESS(addr[13:0]),
		.DATAIN(wdata[31:16]),
		.MASKWREN({wen[3], wen[3], wen[2], wen[2]}),
		.WREN(wen[3]|wen[2]),
		.CHIPSELECT(cs_0),
		.CLOCK(clk),
		.STANDBY(1'b0),
		.SLEEP(1'b0),
		.POWEROFF(1'b1),
		.DATAOUT(rdata_0[31:16])
	);

	SB_SPRAM256KA ram10 (
		.ADDRESS(addr[13:0]),
		.DATAIN(wdata[15:0]),
		.MASKWREN({wen[1], wen[1], wen[0], wen[0]}),
		.WREN(wen[1]|wen[0]),
		.CHIPSELECT(cs_1),
		.CLOCK(clk),
		.STANDBY(1'b0),
		.SLEEP(1'b0),
		.POWEROFF(1'b1),
		.DATAOUT(rdata_1[15:0])
	);

	SB_SPRAM256KA ram11 (
		.ADDRESS(addr[13:0]),
		.DATAIN(wdata[31:16]),
		.MASKWREN({wen[3], wen[3], wen[2], wen[2]}),
		.WREN(wen[3]|wen[2]),
		.CHIPSELECT(cs_1),
		.CLOCK(clk),
		.STANDBY(1'b0),
		.SLEEP(1'b0),
		.POWEROFF(1'b1),
		.DATAOUT(rdata_1[31:16])
	);

endmodule
