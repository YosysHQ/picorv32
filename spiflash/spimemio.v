module spimemio (
	input clk, resetn,

	input valid,
	output reg ready,
	input [23:0] addr,
	output reg [31:0] rdata,

	output reg spi_cs,
	output reg spi_sclk,
	output reg spi_mosi,
	input spi_miso
);
	reg [23:0] addr_q;
	reg addr_q_vld;

	reg [31:0] buffer;
	reg [6:0] xfer_cnt;
	reg xfer_wait;

	always @(posedge clk) begin
		ready <= 0;
		if (!resetn) begin
			spi_cs <= 1;
			spi_sclk <= 1;
			xfer_cnt <= 8;
			buffer <= 8'hAB << 24;
			addr_q_vld <= 0;
			xfer_wait <= 0;
		end else
		if (xfer_cnt) begin
			if (spi_cs) begin
				spi_cs <= 0;
			end else
			if (spi_sclk) begin
				spi_sclk <= 0;
				spi_mosi <= buffer[31];
			end else begin
				spi_sclk <= 1;
				buffer <= {buffer, spi_miso};
				xfer_cnt <= xfer_cnt - 1;
			end
		end else
		if (xfer_wait) begin
			ready <= 1;
			rdata <= {buffer[7:0], buffer[15:8], buffer[23:16], buffer[31:24]};
			xfer_wait <= 0;
		end else
		if (valid && !ready) begin
			if (addr_q_vld && addr_q == addr) begin
				addr_q <= addr + 4;
				addr_q_vld <= 1;
				xfer_cnt <= 32;
				xfer_wait <= 1;
			end else begin
				spi_cs <= 1;
				buffer <= {8'h 03, addr};
				addr_q <= addr + 4;
				addr_q_vld <= 1;
				xfer_cnt <= 64;
				xfer_wait <= 1;
			end
		end
	end
endmodule
