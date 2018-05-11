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
	reg flash_csb = 1;
	reg flash_clk = 0;

	wire flash_io0;
	wire flash_io1;
	wire flash_io2;
	wire flash_io3;

	reg flash_io0_oe = 0;
	reg flash_io1_oe = 0;
	reg flash_io2_oe = 0;
	reg flash_io3_oe = 0;

	reg flash_io0_dout = 0;
	reg flash_io1_dout = 0;
	reg flash_io2_dout = 0;
	reg flash_io3_dout = 0;

	assign flash_io0 = flash_io0_oe ? flash_io0_dout : 1'bz;
	assign flash_io1 = flash_io1_oe ? flash_io1_dout : 1'bz;
	assign flash_io2 = flash_io2_oe ? flash_io2_dout : 1'bz;
	assign flash_io3 = flash_io3_oe ? flash_io3_dout : 1'bz;

	spiflash uut (
		.csb(flash_csb),
		.clk(flash_clk),
		.io0(flash_io0),
		.io1(flash_io1),
		.io2(flash_io2),
		.io3(flash_io3)
	);

	localparam [23:0] offset = 24'h100000;
	localparam [31:0] word0 = 32'h 00000093;
	localparam [31:0] word1 = 32'h 00000193;

	reg [7:0] rdata;
	integer errcount = 0;

	task expect;
		input [7:0] data;
		begin
			if (data !== rdata) begin
				$display("ERROR: Got %x (%b) but expected %x (%b).", rdata, rdata, data, data);
				errcount = errcount + 1;
			end
		end
	endtask

	task xfer_begin;
		begin
			#5;
			flash_csb = 0;
			$display("-- BEGIN");
			#5;
		end
	endtask

	task xfer_dummy;
		begin
			flash_io0_oe = 0;
			flash_io1_oe = 0;
			flash_io2_oe = 0;
			flash_io3_oe = 0;

			#5;
			flash_clk = 1;
			#5;
			flash_clk = 0;
			#5;
		end
	endtask

	task xfer_end;
		begin
			#5;
			flash_csb = 1;
			flash_io0_oe = 0;
			flash_io1_oe = 0;
			flash_io2_oe = 0;
			flash_io3_oe = 0;
			$display("-- END");
			$display("");
			#5;
		end
	endtask

	task xfer_spi;
		input [7:0] data;
		integer i;
		begin
			flash_io0_oe = 1;
			flash_io1_oe = 0;
			flash_io2_oe = 0;
			flash_io3_oe = 0;

			for (i = 0; i < 8; i=i+1) begin
				flash_io0_dout = data[7-i];
				#5;
				flash_clk = 1;
				rdata[7-i] = flash_io1;
				#5;
				flash_clk = 0;
			end

			$display("--  SPI SDR  %02x %02x", data, rdata);
			#5;
		end
	endtask

	task xfer_qspi_wr;
		input [7:0] data;
		integer i;
		begin
			flash_io0_oe = 1;
			flash_io1_oe = 1;
			flash_io2_oe = 1;
			flash_io3_oe = 1;

			flash_io0_dout = data[4];
			flash_io1_dout = data[5];
			flash_io2_dout = data[6];
			flash_io3_dout = data[7];

			#5;
			flash_clk = 1;

			#5;
			flash_clk = 0;
			flash_io0_dout = data[0];
			flash_io1_dout = data[1];
			flash_io2_dout = data[2];
			flash_io3_dout = data[3];

			#5;
			flash_clk = 1;
			#5;
			flash_clk = 0;

			$display("-- QSPI SDR  %02x --", data);
			#5;
		end
	endtask

	task xfer_qspi_rd;
		integer i;
		begin
			flash_io0_oe = 0;
			flash_io1_oe = 0;
			flash_io2_oe = 0;
			flash_io3_oe = 0;

			#5;
			flash_clk = 1;
			rdata[4] = flash_io0;
			rdata[5] = flash_io1;
			rdata[6] = flash_io2;
			rdata[7] = flash_io3;

			#5;
			flash_clk = 0;

			#5;
			flash_clk = 1;
			rdata[0] = flash_io0;
			rdata[1] = flash_io1;
			rdata[2] = flash_io2;
			rdata[3] = flash_io3;

			#5;
			flash_clk = 0;

			$display("-- QSPI SDR  -- %02x", rdata);
			#5;
		end
	endtask

	task xfer_qspi_ddr_wr;
		input [7:0] data;
		integer i;
		begin
			flash_io0_oe = 1;
			flash_io1_oe = 1;
			flash_io2_oe = 1;
			flash_io3_oe = 1;

			flash_io0_dout = data[4];
			flash_io1_dout = data[5];
			flash_io2_dout = data[6];
			flash_io3_dout = data[7];

			#5;
			flash_clk = 1;
			flash_io0_dout = data[0];
			flash_io1_dout = data[1];
			flash_io2_dout = data[2];
			flash_io3_dout = data[3];

			#5;
			flash_clk = 0;

			$display("-- QSPI DDR  %02x --", data);
			#5;
		end
	endtask

	task xfer_qspi_ddr_rd;
		integer i;
		begin
			flash_io0_oe = 0;
			flash_io1_oe = 0;
			flash_io2_oe = 0;
			flash_io3_oe = 0;

			#5;
			flash_clk = 1;
			rdata[4] = flash_io0;
			rdata[5] = flash_io1;
			rdata[6] = flash_io2;
			rdata[7] = flash_io3;

			#5;
			flash_clk = 0;
			rdata[0] = flash_io0;
			rdata[1] = flash_io1;
			rdata[2] = flash_io2;
			rdata[3] = flash_io3;

			$display("-- QSPI DDR  -- %02x", rdata);
			#5;
		end
	endtask

	initial begin
		$dumpfile("spiflash_tb.vcd");
		$dumpvars(0, testbench);
		$display("");

		$display("Reset (FFh)");
		xfer_begin;
		xfer_spi(8'h ff);
		xfer_end;

		$display("Power Up (ABh)");
		xfer_begin;
		xfer_spi(8'h ab);
		xfer_end;

		$display("Read Data (03h)");
		xfer_begin;
		xfer_spi(8'h 03);
		xfer_spi(offset[23:16]);
		xfer_spi(offset[15:8]);
		xfer_spi(offset[7:0]);
		xfer_spi(8'h 00); expect(word0[7:0]);
		xfer_spi(8'h 00); expect(word0[15:8]);
		xfer_spi(8'h 00); expect(word0[23:16]);
		xfer_spi(8'h 00); expect(word0[31:24]);
		xfer_spi(8'h 00); expect(word1[7:0]);
		xfer_spi(8'h 00); expect(word1[15:8]);
		xfer_spi(8'h 00); expect(word1[23:16]);
		xfer_spi(8'h 00); expect(word1[31:24]);
		xfer_end;

		$display("Quad I/O Read (EBh)");
		xfer_begin;
		xfer_spi(8'h eb);
		xfer_qspi_wr(offset[23:16]);
		xfer_qspi_wr(offset[15:8]);
		xfer_qspi_wr(offset[7:0]);
		xfer_qspi_wr(8'h a5);
		repeat (8) xfer_dummy;
		xfer_qspi_rd; expect(word0[7:0]);
		xfer_qspi_rd; expect(word0[15:8]);
		xfer_qspi_rd; expect(word0[23:16]);
		xfer_qspi_rd; expect(word0[31:24]);
		xfer_qspi_rd; expect(word1[7:0]);
		xfer_qspi_rd; expect(word1[15:8]);
		xfer_qspi_rd; expect(word1[23:16]);
		xfer_qspi_rd; expect(word1[31:24]);
		xfer_end;

		$display("Continous Quad I/O Read");
		xfer_begin;
		xfer_qspi_wr(offset[23:16]);
		xfer_qspi_wr(offset[15:8]);
		xfer_qspi_wr(offset[7:0]);
		xfer_qspi_wr(8'h ff);
		repeat (8) xfer_dummy;
		xfer_qspi_rd; expect(word0[7:0]);
		xfer_qspi_rd; expect(word0[15:8]);
		xfer_qspi_rd; expect(word0[23:16]);
		xfer_qspi_rd; expect(word0[31:24]);
		xfer_qspi_rd; expect(word1[7:0]);
		xfer_qspi_rd; expect(word1[15:8]);
		xfer_qspi_rd; expect(word1[23:16]);
		xfer_qspi_rd; expect(word1[31:24]);
		xfer_end;

		$display("DDR Quad I/O Read (EDh)");
		xfer_begin;
		xfer_spi(8'h ed);
		xfer_qspi_ddr_wr(offset[23:16]);
		xfer_qspi_ddr_wr(offset[15:8]);
		xfer_qspi_ddr_wr(offset[7:0]);
		xfer_qspi_ddr_wr(8'h a5);
		repeat (8) xfer_dummy;
		xfer_qspi_ddr_rd; expect(word0[7:0]);
		xfer_qspi_ddr_rd; expect(word0[15:8]);
		xfer_qspi_ddr_rd; expect(word0[23:16]);
		xfer_qspi_ddr_rd; expect(word0[31:24]);
		xfer_qspi_ddr_rd; expect(word1[7:0]);
		xfer_qspi_ddr_rd; expect(word1[15:8]);
		xfer_qspi_ddr_rd; expect(word1[23:16]);
		xfer_qspi_ddr_rd; expect(word1[31:24]);
		xfer_end;

		$display("Continous DDR Quad I/O Read");
		xfer_begin;
		xfer_qspi_ddr_wr(offset[23:16]);
		xfer_qspi_ddr_wr(offset[15:8]);
		xfer_qspi_ddr_wr(offset[7:0]);
		xfer_qspi_ddr_wr(8'h ff);
		repeat (8) xfer_dummy;
		xfer_qspi_ddr_rd; expect(word0[7:0]);
		xfer_qspi_ddr_rd; expect(word0[15:8]);
		xfer_qspi_ddr_rd; expect(word0[23:16]);
		xfer_qspi_ddr_rd; expect(word0[31:24]);
		xfer_qspi_ddr_rd; expect(word1[7:0]);
		xfer_qspi_ddr_rd; expect(word1[15:8]);
		xfer_qspi_ddr_rd; expect(word1[23:16]);
		xfer_qspi_ddr_rd; expect(word1[31:24]);
		xfer_end;

		#5;

		if (errcount) begin
			$display("FAIL");
			$stop;
		end else begin
			$display("PASS");
		end
	end
endmodule
