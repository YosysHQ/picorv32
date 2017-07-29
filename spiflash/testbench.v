module testbench;
	reg clk = 1;
	always #5 clk = ~clk;

	initial begin
		$dumpfile("testbench.vcd");
		$dumpvars(0, testbench);
		repeat (10000) @(posedge clk);
		$display("<END>");
		$finish;
	end

	wire [31:0] gpio_i = 0;
	wire [31:0] gpio_o;

	wire spi_cs;
	wire spi_sclk;
	wire spi_mosi;
	wire spi_miso;

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
