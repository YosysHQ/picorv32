`timescale 1 ns / 1 ps

module testbench;
	reg clk = 1;
	always #5 clk = ~clk;
	wire LED0, LED1, LED2, LED3, LED4, LED5, LED6, LED7;

	top uut (
		.clk(clk),
		.LED0(LED0),
		.LED1(LED1),
		.LED2(LED2),
		.LED3(LED3),
		.LED4(LED4),
		.LED5(LED5),
		.LED6(LED6),
		.LED7(LED7)
	);

	initial begin
		if ($test$plusargs("vcd")) begin
			$dumpfile("example.vcd");
			$dumpvars(0, testbench);
		end

		$monitor(LED7, LED6, LED5, LED4, LED3, LED2, LED1, LED0);
		repeat (10000) @(posedge clk);
		$finish;
	end
endmodule
