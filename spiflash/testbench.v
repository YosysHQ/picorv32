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

	wire spi_cs;
	wire spi_sclk;
	wire spi_mosi;
	wire spi_miso;

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

	top uut (
		.clk     (clk     ),
		.gpio_i  (gpio_i  ),
		.gpio_o  (gpio_o  ),
		.spi_cs  (spi_cs  ),
		.spi_sclk(spi_sclk),
		.spi_mosi(spi_mosi),
		.spi_miso(spi_miso)
	);

	spiflash spiflash (
		.spi_cs  (spi_cs  ),
		.spi_sclk(spi_sclk),
		.spi_mosi(spi_mosi),
		.spi_miso(spi_miso)
	);
endmodule
