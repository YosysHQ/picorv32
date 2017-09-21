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

module spimemio (
	input clk, resetn,

	input valid,
	output ready,
	input [23:0] addr,
	output reg [31:0] rdata,

	output flash_csb,
	output flash_clk,

	output flash_io0_oe,
	output flash_io1_oe,
	output flash_io2_oe,
	output flash_io3_oe,

	output flash_io0_do,
	output flash_io1_do,
	output flash_io2_do,
	output flash_io3_do,

	input  flash_io0_di,
	input  flash_io1_di,
	input  flash_io2_di,
	input  flash_io3_di,

	input   [3:0] cfgreg_we,
	input  [31:0] cfgreg_di,
	output [31:0] cfgreg_do
);
	reg        xfer_resetn;
	reg        din_valid;
	wire       din_ready;
	reg  [7:0] din_data;
	reg  [3:0] din_tag;
	reg        din_cont;
	reg        din_qspi;
	reg        din_ddr;
	reg        din_rd;

	wire       dout_valid;
	wire [7:0] dout_data;
	wire [3:0] dout_tag;

	reg [23:0] buffer;

	reg [23:0] rd_addr;
	reg rd_valid;
	reg rd_wait;
	reg rd_inc;

	assign ready = valid && (addr == rd_addr) && rd_valid;
	wire jump = valid && !ready && (addr != rd_addr+4) && rd_valid;

	reg softreset;

	reg       config_en;      // cfgreg[31]
	reg       config_ddr;     // cfgreg[22]
	reg       config_qspi;    // cfgreg[21]
	reg       config_cont;    // cfgreg[20]
	reg [3:0] config_dummy;   // cfgreg[19:16]
	reg [3:0] config_oe;      // cfgreg[11:8]
	reg       config_csb;     // cfgreg[5]
	reg       config_clk;     // cfgref[4]
	reg [3:0] config_do;      // cfgreg[3:0]

	assign cfgreg_do[31] = config_en;
	assign cfgreg_do[30:23] = 0;
	assign cfgreg_do[22] = config_ddr;
	assign cfgreg_do[21] = config_qspi;
	assign cfgreg_do[20] = config_cont;
	assign cfgreg_do[19:16] = config_dummy;
	assign cfgreg_do[15:12] = 0;
	assign cfgreg_do[11:8] = {flash_io3_oe, flash_io2_oe, flash_io1_oe, flash_io0_oe};
	assign cfgreg_do[7:6] = 0;
	assign cfgreg_do[5] = flash_csb;
	assign cfgreg_do[4] = flash_clk;
	assign cfgreg_do[3:0] = {flash_io3_di, flash_io2_di, flash_io1_di, flash_io0_di};

	always @(posedge clk) begin
		softreset <= !config_en || cfgreg_we;
		if (!resetn) begin
			softreset <= 1;
			config_en <= 1;
			config_csb <= 0;
			config_clk <= 0;
			config_oe <= 0;
			config_do <= 0;
			config_ddr <= 0;
			config_qspi <= 0;
			config_cont <= 0;
			config_dummy <= 8;
		end else begin
			if (cfgreg_we[0]) begin
				config_csb <= cfgreg_di[5];
				config_clk <= cfgreg_di[4];
				config_do <= cfgreg_di[3:0];
			end
			if (cfgreg_we[1]) begin
				config_oe <= cfgreg_di[11:8];
			end
			if (cfgreg_we[2]) begin
				config_ddr <= cfgreg_di[22];
				config_qspi <= cfgreg_di[21];
				config_cont <= cfgreg_di[20];
				config_dummy <= cfgreg_di[19:16];
			end
			if (cfgreg_we[3]) begin
				config_en <= cfgreg_di[31];
			end
		end
	end

	wire xfer_csb;
	wire xfer_clk;

	wire xfer_io0_oe;
	wire xfer_io1_oe;
	wire xfer_io2_oe;
	wire xfer_io3_oe;

	wire xfer_io0_do;
	wire xfer_io1_do;
	wire xfer_io2_do;
	wire xfer_io3_do;

	reg xfer_io0_90;
	reg xfer_io1_90;
	reg xfer_io2_90;
	reg xfer_io3_90;

	always @(negedge clk) begin
		xfer_io0_90 <= xfer_io0_do;
		xfer_io1_90 <= xfer_io1_do;
		xfer_io2_90 <= xfer_io2_do;
		xfer_io3_90 <= xfer_io3_do;
	end

	assign flash_csb = config_en ? xfer_csb : config_csb;
	assign flash_clk = config_en ? xfer_clk : config_clk;

	assign flash_io0_oe = config_en ? xfer_io0_oe : config_oe[0];
	assign flash_io1_oe = config_en ? xfer_io1_oe : config_oe[1];
	assign flash_io2_oe = config_en ? xfer_io2_oe : config_oe[2];
	assign flash_io3_oe = config_en ? xfer_io3_oe : config_oe[3];

	assign flash_io0_do = config_en ? (config_ddr ? xfer_io0_90 : xfer_io0_do) : config_do[0];
	assign flash_io1_do = config_en ? (config_ddr ? xfer_io1_90 : xfer_io1_do) : config_do[1];
	assign flash_io2_do = config_en ? (config_ddr ? xfer_io2_90 : xfer_io2_do) : config_do[2];
	assign flash_io3_do = config_en ? (config_ddr ? xfer_io3_90 : xfer_io3_do) : config_do[3];

	wire xfer_dspi = din_ddr && !din_qspi;
	wire xfer_ddr = din_ddr && din_qspi;

	spimemio_xfer xfer (
		.clk          (clk         ),
		.resetn       (xfer_resetn ),
		.din_valid    (din_valid   ),
		.din_ready    (din_ready   ),
		.din_data     (din_data    ),
		.din_tag      (din_tag     ),
		.din_cont     (din_cont    ),
		.din_dspi     (xfer_dspi   ),
		.din_qspi     (din_qspi    ),
		.din_ddr      (xfer_ddr    ),
		.din_rd       (din_rd      ),
		.dout_valid   (dout_valid  ),
		.dout_data    (dout_data   ),
		.dout_tag     (dout_tag    ),
		.flash_csb    (xfer_csb    ),
		.flash_clk    (xfer_clk    ),
		.flash_io0_oe (xfer_io0_oe ),
		.flash_io1_oe (xfer_io1_oe ),
		.flash_io2_oe (xfer_io2_oe ),
		.flash_io3_oe (xfer_io3_oe ),
		.flash_io0_do (xfer_io0_do ),
		.flash_io1_do (xfer_io1_do ),
		.flash_io2_do (xfer_io2_do ),
		.flash_io3_do (xfer_io3_do ),
		.flash_io0_di (flash_io0_di),
		.flash_io1_di (flash_io1_di),
		.flash_io2_di (flash_io2_di),
		.flash_io3_di (flash_io3_di)
	);

	reg [3:0] state;

	always @(posedge clk) begin
		xfer_resetn <= 1;
		din_valid <= 0;

		if (!resetn || softreset) begin
			state <= 0;
			xfer_resetn <= 0;
			rd_valid <= 0;
			din_tag <= 0;
			din_cont <= 0;
			din_qspi <= 0;
			din_ddr <= 0;
			din_rd <= 0;
		end else begin
			if (dout_valid && dout_tag == 1) buffer[ 7: 0] <= dout_data;
			if (dout_valid && dout_tag == 2) buffer[15: 8] <= dout_data;
			if (dout_valid && dout_tag == 3) buffer[23:16] <= dout_data;
			if (dout_valid && dout_tag == 4) begin
				rdata <= {dout_data, buffer};
				rd_addr <= rd_inc ? rd_addr + 4 : addr;
				rd_valid <= 1;
				rd_wait <= rd_inc;
				rd_inc <= 1;
			end

			if (valid)
				rd_wait <= 0;

			case (state)
				0: begin
					din_valid <= 1;
					din_data <= 8'h ff;
					din_tag <= 0;
					if (din_ready) begin
						din_valid <= 0;
						state <= 1;
					end
				end
				1: begin
					if (dout_valid) begin
						xfer_resetn <= 0;
						state <= 2;
					end
				end
				2: begin
					din_valid <= 1;
					din_data <= 8'h ab;
					din_tag <= 0;
					if (din_ready) begin
						din_valid <= 0;
						state <= 3;
					end
				end
				3: begin
					if (dout_valid) begin
						xfer_resetn <= 0;
						state <= 4;
					end
				end
				4: begin
					rd_inc <= 0;
					din_valid <= 1;
					din_tag <= 0;
					case ({config_ddr, config_qspi})
						2'b11: din_data <= 8'h ED;
						2'b01: din_data <= 8'h EB;
						2'b10: din_data <= 8'h BB;
						2'b00: din_data <= 8'h 03;
					endcase
					if (din_ready) begin
						din_valid <= 0;
						state <= 5;
					end
				end
				5: begin
					if (valid && !ready) begin
						din_valid <= 1;
						din_tag <= 0;
						din_data <= addr[23:16];
						din_qspi <= config_qspi;
						din_ddr <= config_ddr;
						if (din_ready) begin
							din_valid <= 0;
							state <= 6;
						end
					end
				end
				6: begin
					din_valid <= 1;
					din_tag <= 0;
					din_data <= addr[15:8];
					if (din_ready) begin
						din_valid <= 0;
						state <= 7;
					end
				end
				7: begin
					din_valid <= 1;
					din_tag <= 0;
					din_data <= addr[7:0];
					if (din_ready) begin
						din_valid <= 0;
						din_data <= 0;
						state <= config_qspi || config_ddr ? 8 : 9;
					end
				end
				8: begin
					din_valid <= 1;
					din_tag <= 0;
					din_data <= config_cont ? 8'h A5 : 8'h FF;
					if (din_ready) begin
						din_rd <= 1;
						din_data <= config_dummy;
						din_valid <= 0;
						state <= 9;
					end
				end
				9: begin
					din_valid <= 1;
					din_tag <= 1;
					if (din_ready) begin
						din_valid <= 0;
						state <= 10;
					end
				end
				10: begin
					din_valid <= 1;
					din_data <= 8'h 00;
					din_tag <= 2;
					if (din_ready) begin
						din_valid <= 0;
						state <= 11;
					end
				end
				11: begin
					din_valid <= 1;
					din_tag <= 3;
					if (din_ready) begin
						din_valid <= 0;
						state <= 12;
					end
				end
				12: begin
					if (!rd_wait || valid) begin
						din_valid <= 1;
						din_tag <= 4;
						if (din_ready) begin
							din_valid <= 0;
							state <= 9;
						end
					end
				end
			endcase

			if (jump) begin
				rd_inc <= 0;
				rd_valid <= 0;
				xfer_resetn <= 0;
				if (config_cont) begin
					state <= 5;
				end else begin
					state <= 4;
					din_qspi <= 0;
					din_ddr <= 0;
				end
				din_rd <= 0;
			end
		end
	end
endmodule

module spimemio_xfer (
	input clk, resetn,

	input            din_valid,
	output           din_ready,
	input      [7:0] din_data,
	input      [3:0] din_tag,
	input            din_cont,
	input            din_dspi,
	input            din_qspi,
	input            din_ddr,
	input            din_rd,

	output           dout_valid,
	output     [7:0] dout_data,
	output     [3:0] dout_tag,

	output reg flash_csb,
	output reg flash_clk,

	output reg flash_io0_oe,
	output reg flash_io1_oe,
	output reg flash_io2_oe,
	output reg flash_io3_oe,

	output reg flash_io0_do,
	output reg flash_io1_do,
	output reg flash_io2_do,
	output reg flash_io3_do,

	input      flash_io0_di,
	input      flash_io1_di,
	input      flash_io2_di,
	input      flash_io3_di
);
	reg [7:0] obuffer;
	reg [7:0] ibuffer;

	reg [3:0] count;
	reg [3:0] dummy_count;

	reg xfer_cont;
	reg xfer_dspi;
	reg xfer_qspi;
	reg xfer_ddr;
	reg xfer_ddr_q;
	reg xfer_rd;
	reg [3:0] xfer_tag;
	reg [3:0] xfer_tag_q;

	reg [7:0] next_obuffer;
	reg [7:0] next_ibuffer;
	reg [3:0] next_count;

	reg fetch;
	reg next_fetch;
	reg last_fetch;

	always @(posedge clk) begin
		xfer_ddr_q <= xfer_ddr;
		xfer_tag_q <= xfer_tag;
	end

	assign din_ready = din_valid && resetn && next_fetch;

	assign dout_valid = (xfer_ddr_q ? fetch && !last_fetch : next_fetch && !fetch) && resetn;
	assign dout_data = ibuffer;
	assign dout_tag = xfer_tag_q;

	always @* begin
		flash_io0_oe = 0;
		flash_io1_oe = 0;
		flash_io2_oe = 0;
		flash_io3_oe = 0;

		flash_io0_do = 0;
		flash_io1_do = 0;
		flash_io2_do = 0;
		flash_io3_do = 0;

		next_obuffer = obuffer;
		next_ibuffer = ibuffer;
		next_count = count;
		next_fetch = 0;

		if (dummy_count == 0) begin
			casez ({xfer_ddr, xfer_qspi, xfer_dspi})
				3'b 000: begin
					flash_io0_oe = 1;
					flash_io0_do = obuffer[7];

					if (flash_clk) begin
						next_obuffer = {obuffer[6:0], 1'b 0};
						next_count = count - |count;
					end else begin
						next_ibuffer = {ibuffer[6:0], flash_io1_di};
					end

					next_fetch = (next_count == 0);
				end
				3'b 01?: begin
					flash_io0_oe = !xfer_rd;
					flash_io1_oe = !xfer_rd;
					flash_io2_oe = !xfer_rd;
					flash_io3_oe = !xfer_rd;

					flash_io0_do = obuffer[4];
					flash_io1_do = obuffer[5];
					flash_io2_do = obuffer[6];
					flash_io3_do = obuffer[7];

					if (flash_clk) begin
						next_obuffer = {obuffer[3:0], 4'b 0000};
						next_count = count - {|count, 2'b00};
					end else begin
						next_ibuffer = {ibuffer[3:0], flash_io3_di, flash_io2_di, flash_io1_di, flash_io0_di};
					end

					next_fetch = (next_count == 0);
				end
				3'b 11?: begin
					flash_io0_oe = !xfer_rd;
					flash_io1_oe = !xfer_rd;
					flash_io2_oe = !xfer_rd;
					flash_io3_oe = !xfer_rd;

					flash_io0_do = obuffer[4];
					flash_io1_do = obuffer[5];
					flash_io2_do = obuffer[6];
					flash_io3_do = obuffer[7];

					next_obuffer = {obuffer[3:0], 4'b 0000};
					next_ibuffer = {ibuffer[3:0], flash_io3_di, flash_io2_di, flash_io1_di, flash_io0_di};
					next_count = count - {|count, 2'b00};

					next_fetch = (next_count == 0);
				end
				3'b ??1: begin
					flash_io0_oe = !xfer_rd;
					flash_io1_oe = !xfer_rd;

					flash_io0_do = obuffer[6];
					flash_io1_do = obuffer[7];

					if (flash_clk) begin
						next_obuffer = {obuffer[5:0], 2'b 00};
						next_count = count - {|count, 1'b0};
					end else begin
						next_ibuffer = {ibuffer[5:0], flash_io1_di, flash_io0_di};
					end

					next_fetch = (next_count == 0);
				end
			endcase
		end
	end

	always @(posedge clk) begin
		if (!resetn) begin
			fetch <= 1;
			last_fetch <= 1;
			flash_csb <= 1;
			flash_clk <= 0;
			count <= 0;
			dummy_count <= 0;
			xfer_tag <= 0;
			xfer_cont <= 0;
			xfer_dspi <= 0;
			xfer_qspi <= 0;
			xfer_ddr <= 0;
			xfer_rd <= 0;
		end else begin
			fetch <= next_fetch;
			last_fetch <= xfer_ddr ? fetch : 1;
			if (dummy_count) begin
				flash_clk <= !flash_clk && !flash_csb;
				dummy_count <= dummy_count - flash_clk;
			end else
			if (count) begin
				flash_clk <= !flash_clk && !flash_csb;
				obuffer <= next_obuffer;
				ibuffer <= next_ibuffer;
				count <= next_count;
			end
			if (din_valid && din_ready) begin
				flash_csb <= 0;
				flash_clk <= 0;

				count <= 8;
				dummy_count <= din_rd ? din_data : 0;
				obuffer <= din_data;

				xfer_tag <= din_tag;
				xfer_cont <= din_cont;
				xfer_dspi <= din_dspi;
				xfer_qspi <= din_qspi;
				xfer_ddr <= din_ddr;
				xfer_rd <= din_rd;
			end
		end
	end
endmodule
