module spiflash (
	input      spi_cs,
	output reg spi_miso,
	input      spi_mosi,
	input      spi_sclk
);
	localparam verbose = 0;
	
	reg [7:0] buffer;
	integer bitcount = 0;
	integer bytecount = 0;

	reg [7:0] spi_cmd;
	reg [23:0] spi_addr;

	reg [7:0] spi_in;
	reg [7:0] spi_out;
	reg spi_io_vld;

	reg powered_up = 0;
	reg in_xfer = 0;

	// 16 MB (128Mb) Flash
	reg [7:0] memory [0:16*1024*1024-1];

	initial begin
		$readmemh("firmware.hex", memory);
	end

	task spi_action;
		begin
			spi_in = buffer;

			if (bytecount == 1) begin
				spi_cmd = buffer;
				if (spi_cmd == 8'hAB)
					powered_up = 1;
				if (spi_cmd == 8'hB9)
					powered_up = 0;
			end

			if (powered_up && spi_cmd == 'h03) begin
				if (bytecount == 2)
					spi_addr[23:16] = buffer;

				if (bytecount == 3)
					spi_addr[15:8] = buffer;

				if (bytecount == 4)
					spi_addr[7:0] = buffer;

				if (bytecount >= 4) begin
					buffer = memory[spi_addr];
					spi_addr = spi_addr + 1;
				end
			end

			spi_out = buffer;
			spi_io_vld = 1;

			if (verbose) begin
				if (bytecount == 1)
					$write("<SPI-START>");
				$write("<SPI:%02x:%02x>", spi_in, spi_out);
			end

		end
	endtask

	always @(spi_cs) begin
		if (spi_cs) begin
			if (verbose && in_xfer) begin
				$display("");
				$fflush;
			end
			buffer = 0;
			in_xfer = 0;
			bitcount = 0;
			bytecount = 0;
			spi_miso = 0;
		end
	end

	always @(spi_cs, spi_sclk) begin
		spi_io_vld = 0;
		if (!spi_cs && !spi_sclk) begin
			spi_miso = buffer[7];
		end
	end

	always @(posedge spi_sclk) begin
		if (!spi_cs) begin
			buffer = {buffer, spi_mosi};
			bitcount = bitcount + 1;
			if (bitcount == 8) begin
				in_xfer = 1;
				bitcount = 0;
				bytecount = bytecount + 1;
				spi_action;
			end
		end
	end
endmodule
