// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

`timescale 1 ns / 1 ps
// `define VERBOSE

module testbench #(
	parameter AXI_TEST = 0,
	parameter VERBOSE = 0
);

	reg clk = 1;
	reg resetn = 0;

	always #5 clk = ~clk;

	initial begin
		repeat (100) @(posedge clk);
		resetn <= 1;
	end

	initial begin
		if ($test$plusargs("vcd")) begin
			$dumpfile("testbench.vcd");
			$dumpvars(0, testbench);
		end
		repeat (1000000) @(posedge clk);
		$display("TIMEOUT");
		$finish;
	end

	picorv32_wrapper #(
		.AXI_TEST (AXI_TEST),
		.VERBOSE  (VERBOSE)
	) top (
		.clk    (clk   ),
		.resetn (resetn)
	);
endmodule
